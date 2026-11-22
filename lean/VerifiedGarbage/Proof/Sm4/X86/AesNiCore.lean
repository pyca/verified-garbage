module

public import VerifiedGarbage.Proof.Sm4.X86.AesNiMaps
public import VerifiedGarbage.Proof.Sm4.Bitsliced
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Layout

/-!
# SM4 by the AES S-box on x86 (32-bit): the core of the modes

`coreSpec`: `Impl.Sm4.X86.AesNi.core` meets what the modes need of a core
(`Proof.Modes.X86.CoreSpec`), with the key a schedule, read through the
first stack argument, and its cipher `Spec.Sm4.cipher`.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNi

open VG VG.X86 VG.X86.ByteMap VG.Impl.Sm4.X86.AesNi
open VG.Proof.Sm4 (sboxB byteAt getLsbD_byteAt getLsbD_tau)
open VG.Spec.Sm4 (Word)
open VG.Proof.Modes.X86 (ScrIn)

/-! ## The byte maps -/

theorem byte_ofNat (b : Byte) : BitVec.ofNat 8 b.toNat = b := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `sbox_all`, of a byte. -/
theorem sbox_ok (b : Byte) :
    am oE (aesSbox (pk b)) = pl (lm1 (sboxB b)) ∧ am oH (aesSbox (pk b)) = pl (lm3 (sboxB b)) ^^^ ch := by
  have h := List.all_eq_true.mp sbox_all b.toNat (List.mem_range.mpr b.isLt)
  rw [byte_ofNat, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h

theorem pv_pl (b : Byte) : pv (pl b) = b := by
  have h := List.all_eq_true.mp inv_all b.toNat (List.mem_range.mpr b.isLt)
  rw [byte_ofNat, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h.1

theorem pk_eq (b : Byte) : pk b = pl b ^^^ pk 0#8 := by
  have h := List.all_eq_true.mp inv_all b.toNat (List.mem_range.mpr b.isLt)
  rw [byte_ofNat, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h.2

/-- A nibble table of the byte maps, of nibbles. -/
theorem lk_xor {t : Nat} (ht : t ∈ [oCV, oCV + 16, oIV, oIV + 16]) {x y : Byte}
    (hx : x.toNat < 16) (hy : y.toNat < 16) : lk t (x ^^^ y) = lk t x ^^^ lk t y := by
  have h := List.all_eq_true.mp lin16_all x.toNat (List.mem_range.mpr hx)
  have h := List.all_eq_true.mp h y.toNat (List.mem_range.mpr hy)
  have h := List.all_eq_true.mp h t ht
  rw [beq_iff_eq, byte_ofNat, byte_ofNat] at h
  rw [← h]
  exact congrArg (lk t) (BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 8) x.isLt y.isLt)]))

theorem lo_lt (b : Byte) : (b &&& 0x0f#8).toNat < 16 := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem hi_lt (b : Byte) : (b >>> 4).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega_using [b.isLt]

/-- The byte maps into and out of the rounds' form are linear. -/
theorem nm_xor {t : Nat} (ht : t = oCV ∨ t = oIV) (u v : Byte) : nm t (u ^^^ v) = nm t u ^^^ nm t v := by
  have e₁ : (u ^^^ v) &&& 0x0f#8 = u &&& 0x0f#8 ^^^ v &&& 0x0f#8 := Fn.lin_xor (g := .and 0x0f#8) rfl u v
  have e₂ : (u ^^^ v) >>> 4 = u >>> 4 ^^^ v >>> 4 := Fn.lin_xor (g := .hi4) rfl u v
  have m₀ : t ∈ [oCV, oCV + 16, oIV, oIV + 16] := by rcases ht with rfl | rfl <;> decide
  have m₁ : t + 16 ∈ [oCV, oCV + 16, oIV, oIV + 16] := by rcases ht with rfl | rfl <;> decide
  unfold nm
  rw [e₁, e₂, lk_xor m₀ (lo_lt u) (lo_lt v), lk_xor m₁ (hi_lt u) (hi_lt v)]
  ac_rfl

theorem pl_xor (u v : Byte) : pl (u ^^^ v) = pl u ^^^ pl v := nm_xor (.inl rfl) u v

/-! ## The bytes of a word -/

theorem byteAt_xor (a b : Word) (k : Nat) : byteAt (a ^^^ b) k = byteAt a k ^^^ byteAt b k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [byteAt, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, hj, decide_true,
    Bool.true_and]

theorem byteAt_tau (x : Word) {k : Nat} (hk : k < 4) : byteAt (Spec.Sm4.tau x) k = sboxB (byteAt x k) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_byteAt _ hk hj, getLsbD_tau x hk hj]

/-- `lm_all`, of a byte. -/
theorem lm_ok (x : Byte) {j : Nat} (hj : j < 8) :
    lm0 x = lm1 x ^^^ lm3 x ∧
    (lm0 x).getLsbD j = (x.getLsbD j ^^ (decide (2 ≤ j) && x.getLsbD (j - 2))) ∧
    (lm1 x).getLsbD j = ((decide (j < 2) && x.getLsbD (j + 6)) ^^ (decide (2 ≤ j) && x.getLsbD (j - 2))) ∧
    (lm3 x).getLsbD j = ((decide (j < 2) && x.getLsbD (j + 6)) ^^ x.getLsbD j) := by
  have h := List.all_eq_true.mp lm_all x.toNat (List.mem_range.mpr x.isLt)
  have h := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [byte_ofNat] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Bit `j` of the byte `k` of a word. -/
def wb (k j : Nat) : Nat := 8 * (3 - k) + j

/-- The bits of a word whose exclusive-or is bit `j` of
`lm0 b[k] ⊕ lm1 b[k+1] ⊕ lm1 b[k+2] ⊕ lm3 b[k+3]`. -/
def rIdx (k j : Nat) : List Nat :=
  [wb k j] ++ (if 2 ≤ j then [wb k (j - 2)] else []) ++
  (if j < 2 then [wb ((k + 1) % 4) (j + 6)] else []) ++ (if 2 ≤ j then [wb ((k + 1) % 4) (j - 2)] else []) ++
  (if j < 2 then [wb ((k + 2) % 4) (j + 6)] else []) ++ (if 2 ≤ j then [wb ((k + 2) % 4) (j - 2)] else []) ++
  (if j < 2 then [wb ((k + 3) % 4) (j + 6)] else []) ++ [wb ((k + 3) % 4) j]

theorem rIdx_perm : ∀ k < 4, ∀ j < 8, (rIdx k j).Perm (Proof.Sm4.linIdx (wb k j)) := by decide

theorem idxXor_append (x : Word) (l l' : List Nat) :
    Proof.Sm4.idxXor x (l ++ l') = (Proof.Sm4.idxXor x l ^^ Proof.Sm4.idxXor x l') := by
  induction l with
  | nil => simp only [List.nil_append, Proof.Sm4.idxXor, List.foldr_nil, Bool.false_xor]
  | cons a l ih =>
    simp only [Proof.Sm4.idxXor, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, Bool.xor_assoc]

theorem idxXor_one (x : Word) (i : Nat) : Proof.Sm4.idxXor x [i] = x.getLsbD i := by
  simp only [Proof.Sm4.idxXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]

theorem idxXor_ite (x : Word) (c : Prop) [Decidable c] (i : Nat) :
    Proof.Sm4.idxXor x (if c then [i] else []) = (decide c && x.getLsbD i) := by
  by_cases h : c
  · rw [ite_eq_left h, idxXor_one, decide_eq_true h, Bool.true_and]
  · rw [ite_eq_right h, decide_eq_false h, Bool.false_and]; rfl

/-- A bit of a byte of a word, where a condition says there is one. -/
theorem cond_bit (B : Word) (c : Prop) [Decidable c] {k j : Nat} (hk : k < 4) (h : c → j < 8) :
    (decide c && (byteAt B k).getLsbD j) = (decide c && B.getLsbD (wb k j)) := by
  by_cases hc : c
  · rw [decide_eq_true hc, Bool.true_and, Bool.true_and, getLsbD_byteAt _ hk (h hc)]; rfl
  · rw [decide_eq_false hc, Bool.false_and, Bool.false_and]

/-- §6.2: a byte of `L(B)`, of the byte there, the two after it, and the
third after it. -/
theorem byteAt_linear (B : Word) {k : Nat} (hk : k < 4) :
    byteAt (Spec.Sm4.linear B) k =
      lm0 (byteAt B k) ^^^ lm1 (byteAt B ((k + 1) % 4)) ^^^ lm1 (byteAt B ((k + 2) % 4)) ^^^
        lm3 (byteAt B ((k + 3) % 4)) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have k1 : (k + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  have k2 : (k + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  have k3 : (k + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [getLsbD_byteAt _ hk hj]
  have hl := Proof.Sm4.getLsbD_fn .enc B (k := 8 * (3 - k) + j) (by omega_using [hk, hj])
  rw [show Impl.Sm4.Lin.fn .enc = Spec.Sm4.linear from rfl] at hl
  rw [hl, show Impl.Sm4.Lin.idx .enc (8 * (3 - k) + j) = Proof.Sm4.linIdx (wb k j) from rfl,
    ← Proof.Sm4.idxXor_perm B (rIdx_perm k hk j hj)]
  simp only [BitVec.getLsbD_xor, (lm_ok _ hj).2.1, (lm_ok _ hj).2.2.1, (lm_ok _ hj).2.2.2]
  rw [getLsbD_byteAt _ hk hj, getLsbD_byteAt _ k3 hj, cond_bit B (2 ≤ j) hk (fun _ => by omega_using [hj]),
    cond_bit B (j < 2) k1 (fun h => by omega_using [h]), cond_bit B (2 ≤ j) k1 (fun _ => by omega_using [hj]),
    cond_bit B (j < 2) k2 (fun h => by omega_using [h]), cond_bit B (2 ≤ j) k2 (fun _ => by omega_using [hj]),
    cond_bit B (j < 2) k3 (fun h => by omega_using [h])]
  simp only [rIdx, idxXor_append, idxXor_ite, idxXor_one, wb, Bool.xor_assoc]

/-! ## The rounds of the specification -/

/-- The state after `i` rounds. -/
def st (rk : Nat → Word) (b : Spec.Sm4.Block) (i : Nat) : Spec.Sm4.State :=
  (List.range i).foldl (fun s i => Spec.Sm4.round (rk i) s) (Spec.Sm4.initial b)

theorem st_succ (rk : Nat → Word) (b : Spec.Sm4.Block) (i : Nat) :
    st rk b (i + 1) = Spec.Sm4.round (rk i) (st rk b i) := by
  rw [st, List.range_succ, List.foldl_append]; rfl

/-! ## What the parts of the block's code compute -/

/-- Byte `o` of the entries at `esi`. -/
def kb (s : State) (o : Nat) : Byte := s.mem ((s.gpr kr).setWidth 64 + BitVec.ofNat 64 o)

/-- What a round needs of the state: the table's address in its register,
the 128 bytes of four entries at `esi` readable, and the mask. -/
structure Env (s : State) : Prop where
  tb : s.gpr tbr = s.syms tableName
  fit : (s.gpr kr).toNat + 128 ≤ 2 ^ 32
  acc : ∀ o, o + 16 ≤ 128 → InRegions (s.rd ++ s.wr) (addr (s.gpr kr) o) 16
  msk : ∀ i < 16, byte (s.xmm m0) i = 0x0f#8

/-- A round's sum at byte `q`, of `aesenclast`'s input bytes `w`. -/
def sig (w : Nat → Byte) (q : Nat) : Byte :=
  am oE (aesSbox (w (srow q))) ^^^ am oH (aesSbox (w (srow q))) ^^^ am oE (aesSbox (w (srow (br 1 q)))) ^^^
    am oE (aesSbox (w (srow (br 2 q)))) ^^^ am oH (aesSbox (w (srow (br 3 q))))

theorem sig_congr {w w' : Nat → Byte} (h : ∀ p < 16, w p = w' p) (q : Nat) : sig w q = sig w' q := by
  unfold sig
  rw [h _ (srow_lt _), h _ (srow_lt _), h _ (srow_lt _), h _ (srow_lt _)]

section
variable {s : State}

theorem Env.rel (h : Env s) : Rel params (envOf params s) regs₀ s :=
  (rel_init (p := params) h.tb h.fit h.acc).const m0 h.msk

theorem env_var (r : XReg) {q : Nat} (hq : q < 16) :
    mask (envOf params s) (var r q) nvars = byte (s.xmm r) q := by
  have hr : r.ctorIdx < 8 := by cases r <;> decide
  rw [var, mask_bit _ (by show 16 * r.ctorIdx + q < 1024; omega_using [hr, hq]), envOf_reg params s r hq]

theorem env_key {o : Nat} (ho : o < 128) : mask (envOf params s) (kv o) nvars = kb s o := by
  rw [kv, mask_bit _ (by show 128 + o < 1024; omega_arith), envOf_key]; rfl

theorem aT_sum (env : Nat → BitVec 8) (t : Nat) (a : XReg) (p : Nat) :
    sum env (aT t a p) = am t (aesSbox (mask env (var a (srow p)) nvars)) := by
  simp only [aT, sum, BitVec.xor_zero]; rfl

theorem sigma_sum (a : XReg) (q : Nat) :
    sum (envOf params s) (sigma a q) = sig (fun p => byte (s.xmm a) p) q := by
  simp only [sigma, sum_append, aT_sum, sig, env_var a (srow_lt _)]

/-- Round `r` of a turn: what it leaves in `c`, in `e` and at its word's
place, of the bytes it starts with. -/
theorem round_wp {a c n e : XReg} {r : Nat} (hok : roundOk a c n e r = true) (hr2 : r < 2) (he : Env s)
    (ho : OutOk params oparams s) :
    WP isa (.block (round a c n e r)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨(s.gpr kw).setWidth 64 + BitVec.ofNat 64 (32 * r), 16⟩] s.mem s'.mem ∧
      (∀ q < 16, byte (s'.xmm c) q = kb s (32 * r + 16 + q) ^^^ kb s (32 * r + 32 + q) ^^^ kb s (32 * r + 80 + q) ^^^
        byte (s.xmm n) q ^^^ sig (fun p => byte (s.xmm a) p) q) ∧
      (∀ q < 16, byte (s'.xmm e) q = kb s (32 * r + 16 + q) ^^^ sig (fun p => byte (s.xmm a) p) q) ∧
      (∀ q < 16, s'.mem ((s.gpr kw).setWidth 64 + BitVec.ofNat 64 (32 * r + q)) =
        kb s (32 * r + 16 + q) ^^^ sig (fun p => byte (s.xmm a) p) q) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  unfold roundOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨hc, hes⟩, cc⟩, ce⟩, co⟩, cin⟩, cm⟩ := hok
  refine runS_wp ho (RelS.init he.rel rfl) hrun fun s' hr => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at cm
  refine ⟨hr.gpr, hr.zf, hr.rd, hr.wr, hr.syms, ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · have := hr.frameIn cin
    rwa [Nat.add_sub_cancel_left] at this
  · rw [hr.rel.bytes hc q hq, BV.same_eval _ (List.all_eq_true.mp cc q (List.mem_range.mpr hq))]
    simp only [BV.eval, mask_xor, sigma_sum, BitVec.xor_zero, env_key (show 32 * r + 16 + q < 128 by omega_arith),
      env_key (show 32 * r + 32 + q < 128 by omega_arith), env_key (show 32 * r + 80 + q < 128 by omega_arith),
      env_var n hq]
  · rw [hr.rel.bytes hes q hq, BV.same_eval _ (List.all_eq_true.mp ce q (List.mem_range.mpr hq))]
    simp only [BV.eval, sigma_sum, BitVec.xor_zero, env_key (show 32 * r + 16 + q < 128 by omega_arith)]
  · refine (hr.out co hq).trans ?_
    simp only [BV.eval, sigma_sum, BitVec.xor_zero, env_key (show 32 * r + 16 + q < 128 by omega_arith)]
  · rw [hr.rel.bytes cm.1 q hq, BV.same_eval _ (List.all_eq_true.mp cm.2 q (List.mem_range.mpr hq)), BV.cst_eval]

end

/-! ## A round, of the words -/

/-- Exclusive-ors of bytes, up to order and pairs that cancel. -/
theorem xor_x3 (a b : Byte) : a ^^^ (a ^^^ b) = b := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
theorem xor_lc (a b c : Byte) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by ac_rfl
macro "xor_norm" : tactic =>
  `(tactic| simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_lc, xor_x3, BitVec.xor_self, BitVec.xor_zero,
    BitVec.zero_xor])

/-- Byte `q` of a register that holds the word `X` in the rounds' form, in
every lane; and of one that holds a round key, or `aesenclast`'s input. -/
def wl (X : Word) (q : Nat) : Byte := pl (byteAt X (q % 4))
def wk (Y : Word) (q : Nat) : Byte := pk (byteAt Y (q % 4))

def Hw (v : BitVec 128) (X : Word) : Prop := ∀ q < 16, byte v q = wl X q
def Hk (v : BitVec 128) (Y : Word) : Prop := ∀ q < 16, byte v q = wk Y q

theorem srow_mod (p : Nat) : srow p % 4 = p % 4 := by unfold srow; omega_arith
theorem br_mod (k q : Nat) : br k q % 4 = (q % 4 + k) % 4 := by unfold br; omega_arith

theorem wl_xor (a b : Word) (q : Nat) : wl (a ^^^ b) q = wl a q ^^^ wl b q := by
  rw [wl, byteAt_xor, pl_xor]; rfl

theorem wk_eq (a : Word) (q : Nat) : wk a q = wl a q ^^^ pk 0#8 := pk_eq _

/-- A round's sum, of `aesenclast`'s input for the word `Y`, is `T(Y)` in
the rounds' form. -/
theorem sig_eq {w : Nat → Byte} {Y : Word} (hw : ∀ p < 16, w p = wk Y p) (q : Nat) :
    sig w q = wl (Spec.Sm4.t Y) q := by
  have k0 : q % 4 < 4 := Nat.mod_lt _ (by decide)
  have k1 : (q % 4 + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  have k2 : (q % 4 + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  have k3 : (q % 4 + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
  have a0 : w (srow q) = pk (byteAt Y (q % 4)) := by rw [hw _ (srow_lt _), wk, srow_mod]
  have a1 : w (srow (br 1 q)) = pk (byteAt Y ((q % 4 + 1) % 4)) := by rw [hw _ (srow_lt _), wk, srow_mod, br_mod]
  have a2 : w (srow (br 2 q)) = pk (byteAt Y ((q % 4 + 2) % 4)) := by rw [hw _ (srow_lt _), wk, srow_mod, br_mod]
  have a3 : w (srow (br 3 q)) = pk (byteAt Y ((q % 4 + 3) % 4)) := by rw [hw _ (srow_lt _), wk, srow_mod, br_mod]
  have r : wl (Spec.Sm4.t Y) q = pl (lm1 (sboxB (byteAt Y (q % 4)))) ^^^ pl (lm3 (sboxB (byteAt Y (q % 4)))) ^^^
      pl (lm1 (sboxB (byteAt Y ((q % 4 + 1) % 4)))) ^^^ pl (lm1 (sboxB (byteAt Y ((q % 4 + 2) % 4)))) ^^^
      pl (lm3 (sboxB (byteAt Y ((q % 4 + 3) % 4)))) := by
    rw [wl, show Spec.Sm4.t Y = Spec.Sm4.linear (Spec.Sm4.tau Y) from rfl, byteAt_linear _ k0,
      byteAt_tau _ k0, byteAt_tau _ k1, byteAt_tau _ k2, byteAt_tau _ k3,
      (lm_ok (sboxB (byteAt Y (q % 4))) (j := 0) (by decide)).1, pl_xor, pl_xor, pl_xor, pl_xor]
  rw [r, sig, a0, a1, a2, a3, (sbox_ok (byteAt Y (q % 4))).1, (sbox_ok (byteAt Y (q % 4))).2,
    (sbox_ok (byteAt Y ((q % 4 + 1) % 4))).1, (sbox_ok (byteAt Y ((q % 4 + 2) % 4))).1,
    (sbox_ok (byteAt Y ((q % 4 + 3) % 4))).2]
  generalize pl (lm1 (sboxB (byteAt Y (q % 4)))) = A
  generalize pl (lm3 (sboxB (byteAt Y (q % 4)))) = B
  generalize pl (lm1 (sboxB (byteAt Y ((q % 4 + 1) % 4)))) = C
  generalize pl (lm1 (sboxB (byteAt Y ((q % 4 + 2) % 4)))) = D
  generalize pl (lm3 (sboxB (byteAt Y ((q % 4 + 3) % 4)))) = E
  generalize ch = F
  xor_norm

/-- The next round's input to `aesenclast`. -/
theorem next_in (x0 x2 x3 tY k' : Word) (q : Nat) :
    wl x0 q ^^^ wk k' q ^^^ wl x2 q ^^^ wl x3 q ^^^ wl tY q = wk (x2 ^^^ x3 ^^^ (x0 ^^^ tY) ^^^ k') q := by
  rw [wk_eq, wk_eq, wl_xor, wl_xor, wl_xor, wl_xor]
  xor_norm

/-! ## The entries in the scratch buffer -/

/-- Byte `o` of the entries in the scratch buffer at `B`. -/
def eAt (m : Mem) (B : BitVec 32) (o : Nat) : Byte := m (B.setWidth 64 + BitVec.ofNat 64 (32 + o))

/-- Entry `i` holds the round key `k`; the word `X`. -/
def KeyAt (m : Mem) (B : BitVec 32) (i : Nat) (k : Word) : Prop := ∀ q < 16, eAt m B (32 * i + q) = wk k q
def WordAt (m : Mem) (B : BitVec 32) (i : Nat) (X : Word) : Prop := ∀ q < 16, eAt m B (32 * i + 16 + q) = wl X q

/-- A byte of the entries outside the 16 bytes a part of the code may have
changed. -/
theorem frame_eAt {m m' : Mem} {B : BitVec 32} {lo o : Nat}
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + lo), 16⟩] m m') (ho : o < lo ∨ lo + 16 ≤ o)
    (hb : o < 2 ^ 32) (hl : lo < 2 ^ 32) : eAt m' B o = eAt m B o := by
  have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (32 + o), 1⟩) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [hb]) (by omega_using [hl])) (show (1 : Nat) ≤ 2 ^ 64 by decide)
    (i := 0) (show (0 : Nat) < 1 by decide)
  rw [BitVec.add_zero] at this
  exact this

theorem KeyAt.frame {m m' : Mem} {B : BitVec 32} {i j : Nat} {k : Word} (h : KeyAt m B i k)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + (32 * j + 16)), 16⟩] m m') (hi : i < 36) (hj : j < 36) :
    KeyAt m' B i k := fun q hq => by
  rw [frame_eAt hf (by omega_using [hq]) (by omega_using [hi, hq]) (by omega_using [hj])]; exact h q hq

theorem WordAt.frame {m m' : Mem} {B : BitVec 32} {i j : Nat} {X : Word} (h : WordAt m B i X)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + (32 * j + 16)), 16⟩] m m') (hi : i < 36) (hj : j < 36)
    (hne : i ≠ j) : WordAt m' B i X := fun q hq => by
  rw [frame_eAt hf (by omega_using [hq, hne]) (by omega_using [hi, hq]) (by omega_using [hj])]; exact h q hq

/-- A state of `crypt` after `n` turns, from the state `s₀` it starts in:
the entries' pointer, the pointer of the words' places, and the table's
address. -/
structure At (s₀ : State) (B : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  kp : s.gpr kr = B + BitVec.ofNat 32 (32 + 64 * n)
  kq : s.gpr kw = B + BitVec.ofNat 32 (176 + 64 * n)

section
variable {s₀ s : State} {B : BitVec 32} {n : Nat}

theorem At.of_gpr {s' : State} (h : At s₀ B n s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) : At s₀ B n s' :=
  ⟨by rw [hg]; exact h.base, by rw [hg]; exact h.esp, hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms,
    by rw [hg]; exact h.tb, by rw [hg]; exact h.kp, by rw [hg]; exact h.kq⟩

theorem At.kr64 (h : At s₀ B n s) (hf : B.toNat + 1224 ≤ 2 ^ 32) (hn : n ≤ 16) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (32 + 64 * n) := by
  rw [h.kp]; exact addr_eq (by omega_arith)

theorem At.krNat (h : At s₀ B n s) (hf : B.toNat + 1224 ≤ 2 ^ 32) (hn : n ≤ 16) :
    (s.gpr kr).toNat = B.toNat + (32 + 64 * n) := by
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 32 + 64 * n) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem At.kw64 (h : At s₀ B n s) (hf : B.toNat + 1224 ≤ 2 ^ 32) (hn : n < 16) :
    (s.gpr kw).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (176 + 64 * n) := by
  rw [h.kq]; exact addr_eq (by omega_arith)

theorem At.kwNat (h : At s₀ B n s) (hf : B.toNat + 1224 ≤ 2 ^ 32) (hn : n < 16) :
    (s.gpr kw).toNat = B.toNat + (176 + 64 * n) := by
  rw [h.kq, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 176 + 64 * n) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem At.key (h : At s₀ B n s) (hf : B.toNat + 1224 ≤ 2 ^ 32) (hn : n ≤ 16) (o : Nat) :
    kb s o = eAt s.mem B (64 * n + o) := by
  rw [kb, h.kr64 hf hn, Offset.add_ofNat_add_ofNat, Nat.add_assoc]; rfl

theorem At.env (h : At s₀ B n s) (hs : ScrIn s₀ B 306) (hn : n ≤ 16) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) :
    Env s := by
  have hf := hs.fit
  have hk := h.krNat hf hn
  refine ⟨by rw [h.tb, h.syms], by omega_arith, fun o ho => ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩, hm⟩
  rw [addr_eq (by omega_arith), h.kr64 hf hn, Offset.add_ofNat_add_ofNat]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem At.ok (h : At s₀ B n s) (hs : ScrIn s₀ B 306) (hn : n < 16) : OutOk params oparams s := by
  have hf := hs.fit
  have hk := h.krNat hf (Nat.le_of_lt hn)
  have hw := h.kwNat hf hn
  refine ⟨by show (s.gpr kw).toNat + 48 ≤ _; omega_arith, fun o ho => ⟨_, by rw [h.wr]; exact hs.wr, ?_⟩, ?_,
    by show (s.gpr kr).toNat + 128 ≤ _; omega_arith⟩
  · show Region.Contains _ (addr (s.gpr kw) o) 16
    have ho' : o + 16 ≤ 48 := ho
    rw [addr_eq (by omega_arith), h.kw64 hf hn, Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · show Region.Disjoint ⟨(s.gpr kr).setWidth 64, 128⟩ ⟨(s.gpr kw).setWidth 64, 48⟩
    rw [h.kr64 hf (Nat.le_of_lt hn), h.kw64 hf hn]
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

/-- Round `r` of turn `n`: round `2 n + r` of the block. -/
theorem round_ok {a c nr e : XReg} {r : Nat} (hok : roundOk a c nr e r = true) (hr2 : r < 2) (hs : ScrIn s₀ B 306)
    (hn : n < 16) (h : At s₀ B n s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {x0 x1 x2 x3 k : Word}
    (hin : Hk (s.xmm a) (x1 ^^^ x2 ^^^ x3 ^^^ k)) (hx3 : Hw (s.xmm nr) x3)
    (w0 : WordAt s.mem B (2 * n + r) x0) (w2 : WordAt s.mem B (2 * n + r + 2) x2) :
    WP isa (.block (round a c nr e r)) s fun s' =>
      At s₀ B n s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr = s.gpr ∧ s'.zf = s.zf ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + (32 * (2 * n + r + 4) + 16)), 16⟩] s.mem s'.mem ∧
      Hw (s'.xmm e) (x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) ∧
      WordAt s'.mem B (2 * n + r + 4) (x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) ∧
      ∀ k', KeyAt s.mem B (2 * n + r + 1) k' →
        Hk (s'.xmm c) (x2 ^^^ x3 ^^^ (x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) ^^^ k') := by
  have hf := hs.fit
  have hle := Nat.le_of_lt hn
  refine WP.mono (round_wp hok hr2 (h.env hs hle hm) (h.ok hs hn)) fun s' ⟨hg, hz, hrd, hwr, hsy, hfr, bc, be, bm, hm'⟩ => ?_
  have sg : ∀ q, sig (fun p => byte (s.xmm a) p) q = wl (Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) q := fun q =>
    sig_eq (fun p hp => hin p hp) q
  have e0 : ∀ q < 16, kb s (32 * r + 16 + q) = wl x0 q := fun q hq => by
    rw [h.key hf hle, show 64 * n + (32 * r + 16 + q) = 32 * (2 * n + r) + 16 + q by omega_arith]; exact w0 q hq
  have e2 : ∀ q < 16, kb s (32 * r + 80 + q) = wl x2 q := fun q hq => by
    rw [h.key hf hle, show 64 * n + (32 * r + 80 + q) = 32 * (2 * n + r + 2) + 16 + q by omega_arith]; exact w2 q hq
  have ha : (s.gpr kw).setWidth 64 + BitVec.ofNat 64 (32 * r) =
      B.setWidth 64 + BitVec.ofNat 64 (32 + (32 * (2 * n + r + 4) + 16)) := by
    rw [h.kw64 hf hn, Offset.add_ofNat_add_ofNat]; congr 2; omega_arith
  refine ⟨h.of_gpr hg hrd hwr hsy, hm', hg, hz, by rw [← ha]; exact hfr, fun q hq => ?_, fun q hq => ?_,
    fun k' hk' q hq => ?_⟩
  · rw [be q hq, e0 q hq, sg, wl_xor]
  · have := bm q hq
    rw [h.kw64 hf hn, Offset.add_ofNat_add_ofNat] at this
    rw [eAt, show 32 + (32 * (2 * n + r + 4) + 16 + q) = 176 + 64 * n + (32 * r + q) by omega_arith, this, e0 q hq, sg,
      wl_xor]
  · have e1 : kb s (32 * r + 32 + q) = wk k' q := by
      rw [h.key hf hle, show 64 * n + (32 * r + 32 + q) = 32 * (2 * n + r + 1) + q by omega_arith]; exact hk' q hq
    rw [bc q hq, e0 q hq, e1, e2 q hq, hx3 q hq, sg]
    exact next_in _ _ _ _ _ _

end

/-! ## The block -/

section
variable {is : List Instr} {Q : State → Prop} {s : State}

/-- `sub d, v`, with the flags and the XMM registers. -/
theorem wp_subi_x {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d - v) → s'.xmm = s.xmm → s'.zf = some (s.gpr d - v == 0) →
      WP isa (.block is) s' Q) : WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl rfl)

theorem wp_addi_x {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d + v) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl)

end

/-- The two look-ups of a byte map are the map. -/
theorem cterms_sum (env : Nat → BitVec 8) (t v : Nat) : sum env (cterms t v) = nm t (mask env v nvars) := by
  simp only [cterms, sum, BitVec.xor_zero]; rfl

/-- A byte of the entries outside the bytes of several stores. -/
theorem frame_eAt_list {m m' : Mem} {B : BitVec 32} {los : List Nat} {o : Nat}
    (hf : Frame (los.map fun lo => (⟨B.setWidth 64 + BitVec.ofNat 64 (32 + lo), 16⟩ : Region)) m m')
    (ho : ∀ lo ∈ los, o < lo ∨ lo + 16 ≤ o) (hb : o < 2 ^ 32) (hl : ∀ lo ∈ los, lo < 2 ^ 32) :
    eAt m' B o = eAt m B o := by
  have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (32 + o), 1⟩) (fun r hr => by
    obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hr
    exact Offset.disjoint _ (by omega_using [ho lo hlo]) (by omega_using [hb]) (by omega_using [hl lo hlo]))
    (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
  rw [BitVec.add_zero] at this
  exact this

theorem wordAt_bits (b : Spec.Sm4.Block) (i k : Nat) :
    (Spec.Sm4.wordAt b i).getLsbD k =
      (b.getD i 0 ++ b.getD (i + 1) 0 ++ b.getD (i + 2) 0 ++ b.getD (i + 3) 0 : BitVec (8 + 8 + 8 + 8)).getLsbD k :=
  rfl

/-- A byte of a word of a block. -/
theorem byteAt_wordAt (b : Spec.Sm4.Block) (i : Nat) {k : Nat} (hk : k < 4) :
    byteAt (Spec.Sm4.wordAt b i) k = b.getD (i + k) 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_byteAt _ hk hj, wordAt_bits]
  simp only [BitVec.getLsbD_append]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega_using [hj]) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.lt_irrefl, Nat.add_zero]

/-- Word `w` of the block at byte 8 of the scratch buffer. -/
def bwd (m : Mem) (B : BitVec 32) (w : Nat) : Word :=
  Spec.Sm4.wordAt (Spec.Sm4.blockAt m (B.setWidth 64 + BitVec.ofNat 64 8)) (4 * w)

theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (Spec.Sm4.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Sm4.blockAt, Vector.getD, hi]

theorem byteAt_bwd (m : Mem) (B : BitVec 32) {w k : Nat} (hw : w < 4) (hk : k < 4) :
    byteAt (bwd m B w) k = m (B.setWidth 64 + BitVec.ofNat 64 (8 + (4 * w + k))) := by
  rw [bwd, byteAt_wordAt _ _ hk, blockAt_getD _ _ (by omega_using [hw, hk]), Offset.add_ofNat_add_ofNat]

section
variable {s : State} {B : BitVec 32}

/-- The block in `xmm0` to its four words in the rounds' form, in the first
four entries; the last word left in `xmm1`, the exclusive-or of the last
three in `xmm0`; and the mask. -/
theorem head_wp (htb : s.gpr tbr = s.syms tableName) (hk : s.gpr kr = B + BitVec.ofNat 32 32)
    (hwr : (⟨B.setWidth 64, 4 * 306⟩ : Region) ∈ s.wr) (hf : B.toNat + 1224 ≤ 2 ^ 32) :
    WP isa (.block headX) s fun s' =>
      s'.gpr = s.gpr ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame ([112, 80, 48, 16].map fun lo => (⟨B.setWidth 64 + BitVec.ofNat 64 (32 + lo), 16⟩ : Region))
        s.mem s'.mem ∧
      (∀ w < 4, ∀ q < 16, eAt s'.mem B (32 * w + 16 + q) = pl (byte (s.xmm .xmm0) (4 * w + q % 4))) ∧
      (∀ q < 16, byte (s'.xmm .xmm0) q = pl (byte (s.xmm .xmm0) (4 + q % 4)) ^^^
        pl (byte (s.xmm .xmm0) (8 + q % 4)) ^^^ pl (byte (s.xmm .xmm0) (12 + q % 4))) ∧
      (∀ q < 16, byte (s'.xmm .xmm1) q = pl (byte (s.xmm .xmm0) (12 + q % 4))) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have k64 : (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 32 := by rw [hk]; exact addr_eq (by omega_arith)
  have kn : (s.gpr kr).toNat = B.toNat + 32 := by
    rw [hk, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 32) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have rel : Rel hparams (envOf hparams s) Regs.init s :=
    rel_init (p := hparams) htb (by show (s.gpr kr).toNat + 0 ≤ _; omega_arith)
      (fun o ho => absurd (show o + 16 ≤ 0 from ho) (by omega_arith))
  have ok : OutOk hparams hoparams s := by
    refine ⟨by show (s.gpr kr).toNat + 128 ≤ _; omega_arith, fun o ho => ⟨_, hwr, ?_⟩, ?_,
      by show (s.gpr kr).toNat + 0 ≤ _; omega_arith⟩
    · show Region.Contains _ (addr (s.gpr kr) o) 16
      have ho' : o + 16 ≤ 128 := ho
      rw [addr_eq (by omega_arith), k64, Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · intro a h₁ _
      simp only [Region.Contains] at h₁
      exact absurd h₁ (by show ¬ _ + 1 ≤ 0; omega_arith)
  have hok := conv_all.1
  unfold headOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, ol⟩, h0⟩, h1⟩, cx⟩, cm⟩ := hok
  refine runS_wp ok (RelS.init rel rfl) hrun fun s' hr => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at cm
  have ev : ∀ w q, q < 16 → (hw w q).eval (envOf hparams s) = pl (byte (s.xmm .xmm0) (4 * w + q % 4)) ∨ 4 ≤ w :=
    fun w q hq => by
    by_cases h4 : 4 ≤ w
    · exact .inr h4
    · refine .inl ?_
      rw [hw, BV.eval, mask_zero, cterms_sum, BitVec.zero_xor, BitVec.xor_zero, AesNi.var,
        mask_bit _ (by show 16 * 0 + (4 * w + q % 4) < 1024; omega_arith),
        envOf_reg hparams s .xmm0 (by omega_arith)]
      rfl
  have ev' : ∀ w < 4, ∀ q < 16, (hw w q).eval (envOf hparams s) = pl (byte (s.xmm .xmm0) (4 * w + q % 4)) :=
    fun w hw4 q hq => (ev w q hq).resolve_right (by omega_arith)
  have st : ∀ {o w : Nat}, outOk σ.2 o (hw w) = true → w < 4 → o = 32 * w + 16 → ∀ q < 16,
      eAt s'.mem B (32 * w + 16 + q) = pl (byte (s.xmm .xmm0) (4 * w + q % 4)) := fun {o w} ho hw4 he q hq => by
    have := hr.out ho hq
    rw [show (s.gpr hoparams.oreg) = s.gpr kr from rfl, k64, Offset.add_ofNat_add_ofNat, ev' w hw4 q hq] at this
    rw [eAt, ← this, he]
  refine ⟨hr.gpr, hr.zf, hr.rd, hr.wr, hr.syms, ?_, fun w hw4 q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · have hfr := hr.frame
    rw [show (σ.2.map fun e => (⟨(s.gpr hoparams.oreg).setWidth 64 + BitVec.ofNat 64 e.1, 16⟩ : Region)) =
        ([112, 80, 48, 16].map fun lo => (⟨B.setWidth 64 + BitVec.ofNat 64 (32 + lo), 16⟩ : Region)) by
      rw [← ol, List.map_map]
      refine List.map_congr_left fun e _ => ?_
      show (⟨(s.gpr kr).setWidth 64 + BitVec.ofNat 64 e.1, 16⟩ : Region) = _
      rw [k64, Offset.add_ofNat_add_ofNat]
      rfl] at hfr
    exact hfr
  · rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw4]) with rfl | rfl | rfl | rfl
    · exact st o0 (by decide) rfl q hq
    · exact st o1 (by decide) rfl q hq
    · exact st o2 (by decide) rfl q hq
    · exact st o3 (by decide) rfl q hq
  · have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cx q (List.mem_range.mpr hq))
    rw [hr.rel.bytes h0 q hq, BV.same_eval _ c.1, BV.xor_eval, BV.xor_eval, ev' 1 (by decide) q hq,
      ev' 2 (by decide) q hq, ev' 3 (by decide) q hq]
  · have c := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp cx q (List.mem_range.mpr hq))
    rw [hr.rel.bytes h1 q hq, BV.same_eval _ c.2, ev' 3 (by decide) q hq]
  · rw [hr.rel.bytes cm.1 q hq, BV.same_eval _ (List.all_eq_true.mp cm.2 q (List.mem_range.mpr hq)), BV.cst_eval]

end

section
variable {s₀ s : State} {B : BitVec 32} {rk : Nat → Word}

/-- The four words of a state, in the entries `j` to `j + 3`. -/
def Words (m : Mem) (B : BitVec 32) (j : Nat) (x : Spec.Sm4.State) : Prop :=
  WordAt m B j x.1 ∧ WordAt m B (j + 1) x.2.1 ∧ WordAt m B (j + 2) x.2.2.1 ∧ WordAt m B (j + 3) x.2.2.2

theorem wk_sum (a b c k : Word) (q : Nat) : wl a q ^^^ wl b q ^^^ wl c q ^^^ wk k q = wk (a ^^^ b ^^^ c ^^^ k) q := by
  rw [wk_eq, wk_eq, wl_xor, wl_xor, wl_xor]
  xor_norm

/-- The block at byte 8 of the scratch buffer to the first four entries,
and `aesenclast`'s input for the first round. -/
theorem cryptHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 306)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (rk i)) :
    WP isa (.block (cryptHead ++ cryptKey)) s fun s' =>
      At s B 0 s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr .eax = BitVec.ofNat 32 16 ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 1152⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (rk i)) ∧
      (∀ w < 4, WordAt s'.mem B w (bwd s.mem B w)) ∧ Hw (s'.xmm .xmm1) (bwd s.mem B 3) ∧
      Hk (s'.xmm .xmm0) (bwd s.mem B 1 ^^^ bwd s.mem B 2 ^^^ bwd s.mem B 3 ^^^ rk 0) := by
  have hf := hs.fit
  have hw : InRegions (s.rd ++ s.wr) (addr B 0) 4 := ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.mov tbr (.mem ⟨Impl.Modes.X86.sb, 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) ::
    .alu .add kr (.imm 32) :: .mov kw (.reg kr) :: .alu .add kw (.imm 144) :: .mov .eax (.imm 16) ::
    .movdquLoad .xmm0 ⟨Impl.Modes.X86.sb, 8⟩ :: (headX ++ cryptKey))) s _
  refine Wp.wp_ldm hB hw fun s₁ u₁ => ?_
  refine Wp.wp_mov fun s₂ u₂ => ?_
  refine Wp.wp_addi fun s₃ u₃ => ?_
  refine Wp.wp_mov fun s₄ u₄ => ?_
  refine Wp.wp_addi fun s₅ u₅ => ?_
  refine Wp.wp_movi fun s₆ u₆ => ?_
  have e₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have w₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have y₆ : s₆.syms = s.syms := by rw [u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have b₆ : s₆.gpr Impl.Modes.X86.sb = B := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have k₆ : s₆.gpr kr = B + BitVec.ofNat 32 32 := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
      u₁.other _ (by decide), hB]
    rfl
  have a₆ : At s B 0 s₆ := by
    refine ⟨b₆, ?_, r₆, w₆, y₆, ?_, k₆, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, addr_eq (by omega_arith), BitVec.add_zero]
      exact htab
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hB,
        show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, show (144 : BitVec 32) = BitVec.ofNat 32 144 from rfl,
        Offset.add_ofNat_add_ofNat]
  have hl : InRegions (s₆.rd ++ s₆.wr) (addr B 8) 16 := ⟨_, List.mem_append_right _ (by rw [w₆]; exact hs.wr), by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine Wp.cons (s' := s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)) ?_ ?_
  · show (s₆.load128 (addr (s₆.gpr Impl.Modes.X86.sb) 8)).map _ = _
    rw [b₆, State.load128, ite_eq_left hl]; rfl
  have hbyte : ∀ k < 16, byte ((s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)).xmm .xmm0) k =
      s.mem (B.setWidth 64 + BitVec.ofNat 64 (8 + k)) := fun k hk => by
    show (s₆.mem.readW (addr B 8) 128).extractLsb' (8 * k) 8 = _
    rw [byte_readW _ _ (by omega_arith), addr_eq (by omega_arith), Offset.add_ofNat_add_ofNat, e₆]
  have a₇ : At s B 0 (s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)) := a₆.of_gpr rfl rfl rfl rfl
  have t₇ : (s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)).gpr tbr =
      (s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)).syms tableName := by
    show s₆.gpr tbr = s₆.syms tableName
    rw [a₆.tb, y₆]
  have w₇ : (⟨B.setWidth 64, 4 * 306⟩ : Region) ∈ (s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)).wr := by
    show _ ∈ s₆.wr
    rw [w₆]; exact hs.wr
  refine WP.block_append_iff.mpr (WP.mono (head_wp (B := B) t₇ k₆ w₇ hf)
    fun s₈ ⟨g₈, _, rd₈, wr₈, sy₈, f₈, wd₈, x0₈, x1₈, m₈⟩ => ?_)
  have a₈ : At s B 0 s₈ := a₇.of_gpr g₈ rd₈ wr₈ sy₈
  have pb : ∀ w < 4, ∀ q < 16, pl (byte ((s₆.setXmm .xmm0 (s₆.mem.readW (addr B 8) 128)).xmm .xmm0) (4 * w + q % 4)) =
      wl (bwd s.mem B w) q := fun w hw4 q hq => by
    rw [hbyte _ (by omega_arith), wl, byteAt_bwd _ _ hw4 (Nat.mod_lt _ (by decide))]
  have f₈' : Frame ([112, 80, 48, 16].map fun lo => (⟨B.setWidth 64 + BitVec.ofNat 64 (32 + lo), 16⟩ : Region))
      s.mem s₈.mem := by
    have f' : Frame _ s₆.mem s₈.mem := f₈
    rwa [e₆] at f'
  have key₈ : ∀ i < 32, KeyAt s₈.mem B i (rk i) := fun i hi q hq => by
    rw [frame_eAt_list f₈' (fun lo hlo => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlo
      omega_using [hlo, hq]) (by omega_arith) (fun lo hlo => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlo
      omega_using [hlo])]
    exact hk i hi q hq
  have hl₈ : InRegions (s₈.rd ++ s₈.wr) (addr (s₈.gpr kr) 0) 16 := ⟨_, List.mem_append_right _ (by rw [a₈.wr]; exact hs.wr), by
    have := a₈.krNat hf (by decide)
    rw [addr_eq (by omega_arith), a₈.kr64 hf (by decide), Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine Wp.cons (s' := s₈.setXmm .xmm3 (s₈.mem.readW (addr (s₈.gpr kr) 0) 128)) ?_ (Wp.cons rfl (WP.block_nil ?_))
  · show (s₈.load128 (addr (s₈.gpr kr) 0)).map _ = _
    rw [State.load128, ite_eq_left hl₈]; rfl
  refine ⟨a₈.of_gpr rfl rfl rfl rfl, fun q hq => m₈ q hq, ?_, ?_, key₈, fun w hw4 q hq => ?_, fun q hq => ?_,
    fun q hq => ?_⟩
  · show s₈.gpr .eax = _
    rw [g₈]
    show s₆.gpr .eax = _
    rw [u₆.gpr]
    rfl
  · show Frame _ s.mem s₈.mem
    refine f₈'.sub fun r hr => ?_
    obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlo
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [show B.setWidth 64 + BitVec.ofNat 64 (32 + lo) = B.setWidth 64 + BitVec.ofNat 64 32 + BitVec.ofNat 64 lo by
      rw [Offset.add_ofNat_add_ofNat]]
    exact Offset.sub_base _ (by omega_using [hlo])
  · show eAt s₈.mem B (32 * w + 16 + q) = _
    rw [wd₈ w hw4 q hq, pb w hw4 q hq]
  · show byte (s₈.xmm .xmm1) q = _
    rw [x1₈ q hq]
    exact pb 3 (by decide) q hq
  · show byte (s₈.xmm .xmm0 ^^^ s₈.mem.readW (addr (s₈.gpr kr) 0) 128) q = _
    have kq : byte (s₈.mem.readW (addr (s₈.gpr kr) 0) 128) q = wk (rk 0) q := by
      have := a₈.krNat hf (by decide)
      show (s₈.mem.readW (addr (s₈.gpr kr) 0) 128).extractLsb' (8 * q) 8 = _
      rw [byte_readW _ _ (by omega_arith), addr_eq (by omega_arith), a₈.kr64 hf (by decide), Offset.add_ofNat_add_ofNat,
        Offset.add_ofNat_add_ofNat]
      exact key₈ 0 (by decide) q hq
    rw [byte_xor, kq, x0₈ q hq]
    have e1 := pb 1 (by decide) q hq
    have e2 := pb 2 (by decide) q hq
    have e3 := pb 3 (by decide) q hq
    rw [show 4 * 1 + q % 4 = 4 + q % 4 from rfl] at e1
    rw [show 4 * 2 + q % 4 = 8 + q % 4 from rfl] at e2
    rw [show 4 * 3 + q % 4 = 12 + q % 4 from rfl] at e3
    rw [e1, e2, e3]
    exact wk_sum _ _ _ _ _

/-- The state with `n` turns left: the pointers after `16 - n` turns, the
turns left in `eax`, the round keys, and the four words of the
specification's state after `2 (16 - n)` rounds in their entries, the last
also in `xmm1`, with `aesenclast`'s input for the next round in `xmm0`. -/
def Inv (s₀ : State) (B : BitVec 32) (rk : Nat → Word) (b : Spec.Sm4.Block) (n : Nat) (s : State) : Prop :=
  n ≤ 16 ∧ At s₀ B (16 - n) s ∧ (∀ q < 16, byte (s.xmm m0) q = 0x0f#8) ∧ s.gpr .eax = BitVec.ofNat 32 n ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 1152⟩] s₀.mem s.mem ∧ (∀ i < 32, KeyAt s.mem B i (rk i)) ∧
    ∃ x0 x1 x2 x3, st rk b (2 * (16 - n)) = (x0, x1, x2, x3) ∧
      WordAt s.mem B (2 * (16 - n)) x0 ∧ WordAt s.mem B (2 * (16 - n) + 1) x1 ∧
      WordAt s.mem B (2 * (16 - n) + 2) x2 ∧ WordAt s.mem B (2 * (16 - n) + 3) x3 ∧
      Hw (s.xmm .xmm1) x3 ∧ (1 ≤ n → Hk (s.xmm .xmm0) (x1 ^^^ x2 ^^^ x3 ^^^ rk (2 * (16 - n))))

theorem entry_sub (B : BitVec 32) {j : Nat} (hj : j < 36) :
    Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 (32 + (32 * j + 16)), 16⟩
      ⟨B.setWidth 64 + BitVec.ofNat 64 32, 1152⟩ :=
  Offset.sub _ (by omega_arith) (by omega_using [hj])

/-- A turn of the loop: two rounds. -/
theorem turn_wp (hs : ScrIn s₀ B 306) {b : Spec.Sm4.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.block turn) s fun s' => s'.zf = some (decide (n = 1)) ∧ Inv s₀ B rk b (n - 1) s' := by
  obtain ⟨hn16, a, hm, hc, hfr, hk, x0, x1, x2, x3, hst, w0, w1, w2, w3, hx3, hin⟩ := hI
  have hin := hin hn
  obtain ⟨m, hm'⟩ : ∃ m, m = 16 - n := ⟨_, rfl⟩
  rw [← hm'] at a hst w0 w1 w2 w3 hin
  have hm16 : m < 16 := by omega_using [hn, hm']
  show WP isa (.block (roundA ++ (roundB ++ Impl.Sm4.X86.AesNi.step))) s _
  refine WP.block_append_iff.mpr (WP.mono (round_ok (r := 0) round_all.1 (by decide) hs hm16 a hm hin hx3 w0 w2)
    fun s₁ ⟨a₁, m₁, g₁, z₁, f₁, e₁, wn₁, c₁⟩ => ?_)
  obtain ⟨x4, hx4⟩ : ∃ x4, x4 = x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ rk (2 * m)) := ⟨_, rfl⟩
  rw [← hx4] at e₁ wn₁ c₁
  have k₁ : ∀ i < 32, KeyAt s₁.mem B i (rk i) := fun i hi =>
    (hk i hi).frame f₁ (by omega_using [hi]) (by omega_using [hm16])
  have w1₁ : WordAt s₁.mem B (2 * m + 1) x1 := w1.frame f₁ (by omega_using [hm16]) (by omega_using [hm16]) (by omega_arith)
  have w2₁ : WordAt s₁.mem B (2 * m + 2) x2 := w2.frame f₁ (by omega_using [hm16]) (by omega_using [hm16]) (by omega_arith)
  have w3₁ : WordAt s₁.mem B (2 * m + 1 + 2) x3 :=
    w3.frame f₁ (by omega_using [hm16]) (by omega_using [hm16]) (by omega_arith)
  have in₁ : Hk (s₁.xmm .xmm4) (x2 ^^^ x3 ^^^ x4 ^^^ rk (2 * m + 1)) := c₁ _ (hk (2 * m + 0 + 1) (by omega_using [hm16]))
  refine WP.block_append_iff.mpr (WP.mono (round_ok (r := 1) round_all.2 (by decide) hs hm16 a₁ m₁ in₁ e₁ w1₁ w3₁)
    fun s₂ ⟨a₂, m₂, g₂, z₂, f₂, e₂, wn₂, c₂⟩ => ?_)
  obtain ⟨x5, hx5⟩ : ∃ x5, x5 = x1 ^^^ Spec.Sm4.t (x2 ^^^ x3 ^^^ x4 ^^^ rk (2 * m + 1)) := ⟨_, rfl⟩
  rw [← hx5] at e₂ wn₂ c₂
  have k₂ : ∀ i < 32, KeyAt s₂.mem B i (rk i) := fun i hi =>
    (k₁ i hi).frame f₂ (by omega_using [hi]) (by omega_using [hm16])
  have w2₂ : WordAt s₂.mem B (2 * m + 2) x2 := w2₁.frame f₂ (by omega_using [hm16]) (by omega_using [hm16]) (by omega_arith)
  have w3₂ : WordAt s₂.mem B (2 * m + 1 + 2) x3 :=
    w3₁.frame f₂ (by omega_using [hm16]) (by omega_using [hm16]) (by omega_arith)
  have w4₂ : WordAt s₂.mem B (2 * m + 0 + 4) x4 :=
    wn₁.frame f₂ (by omega_using [hm16]) (by omega_using [hm16]) (by omega_arith)
  have c₀ : s₂.gpr .eax = BitVec.ofNat 32 n := by rw [g₂, g₁, hc]
  show WP isa (.block [.alu .add kr (.imm 64), .alu .add kw (.imm 64), .alu .sub .eax (.imm 1)]) s₂ _
  refine wp_addi_x fun s₃ u₃ x₃ => wp_addi_x fun s₄ u₄ x₄ => wp_subi_x fun s₅ u₅ x₅ z₅ => WP.block_nil ?_
  have e₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have xe : s₅.xmm = s₂.xmm := by rw [x₅, x₄, x₃]
  have c₄ : s₄.gpr .eax = BitVec.ofNat 32 n := by rw [u₄.other _ (by decide), u₃.other _ (by decide), c₀]
  refine ⟨?_, by omega_using [hn16], ?_, by rw [xe]; exact m₂, ?_, ?_, by rw [e₅]; exact k₂, x2, x3, x4, x5, ?_, ?_,
    ?_, ?_, ?_, by rw [xe]; exact e₂, fun h1 => ?_⟩
  · rw [z₅, c₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn16]) (by decide)]
  · rw [show 16 - (n - 1) = m + 1 by omega_using [hn, hm', hn16]]
    refine ⟨?_, ?_, by rw [u₅.rd, u₄.rd, u₃.rd]; exact a₂.rd, by rw [u₅.wr, u₄.wr, u₃.wr]; exact a₂.wr,
      by rw [u₅.syms, u₄.syms, u₃.syms]; exact a₂.syms, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]; exact a₂.base
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]; exact a₂.esp
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]; exact a₂.tb
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, a₂.kp,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, Offset.add_ofNat_add_ofNat]
      congr 2
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), a₂.kq,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, Offset.add_ofNat_add_ofNat]
      congr 2
  · rw [u₅.gpr, c₄]; exact Wp.ofNat_pred hn
  · rw [e₅]
    exact (hfr.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact entry_sub B (by omega_using [hm16])⟩)).trans
      (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact entry_sub B (by omega_using [hm16])⟩)
  · rw [show 2 * (16 - (n - 1)) = 2 * m + 1 + 1 by omega_using [hn, hm', hn16], st_succ, st_succ, hst, hx5, hx4]
    rfl
  · rw [e₅, show 2 * (16 - (n - 1)) = 2 * m + 2 by omega_using [hn, hm', hn16]]; exact w2₂
  · rw [e₅, show 2 * (16 - (n - 1)) + 1 = 2 * m + 1 + 2 by omega_using [hn, hm', hn16]]; exact w3₂
  · rw [e₅, show 2 * (16 - (n - 1)) + 2 = 2 * m + 0 + 4 by omega_using [hn, hm', hn16]]; exact w4₂
  · rw [e₅, show 2 * (16 - (n - 1)) + 3 = 2 * m + 1 + 4 by omega_using [hn, hm', hn16]]; exact wn₂
  · rw [xe, show 2 * (16 - (n - 1)) = 2 * m + 1 + 1 by omega_using [hn, hm', hn16]]
    exact c₂ _ (k₁ (2 * m + 1 + 1) (by omega_using [h1, hn, hm', hn16]))

/-- The 16 turns: the four words after the 32 rounds, in the entries 32 to 35. -/
theorem loop_wp (hs : ScrIn s₀ B 306) {b : Spec.Sm4.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.loop (.block turn) .ne) s (Inv s₀ B rk b 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ Inv s₀ B rk b n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (turn_wp hs hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

/-- The last four words to the block, at byte 8 of the scratch buffer. -/
theorem cryptTail_wp (hs : ScrIn s₀ B 306) (h : At s₀ B 16 s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8)
    {x : Nat → Word} (hw : ∀ w < 4, WordAt s.mem B (32 + w) (x w)) :
    WP isa (.block cryptTail) s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s₀.gpr .esp ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.syms = s₀.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 8, 16⟩] s.mem s'.mem ∧
      ∀ q < 16, s'.mem (B.setWidth 64 + BitVec.ofNat 64 8 + BitVec.ofNat 64 q) = byteAt (x (3 - q / 4)) (q % 4) := by
  have hf := hs.fit
  have he := h.env hs (Nat.le_refl 16) hm
  have hok := conv_all.2
  unfold tailOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨h2, c2⟩ := hok
  refine WP.block_append_iff.mpr (run_wp he.rel hrun fun s₁ hr hsame => ?_)
  have v : ∀ q < 16, byte (s₁.xmm .xmm2) q = byteAt (x (3 - q / 4)) (q % 4) := fun q hq => by
    have h4 : q % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [hr.bytes h2 q hq, BV.same_eval _ (List.all_eq_true.mp c2 q (List.mem_range.mpr hq)), BV.eval, mask_zero,
      cterms_sum, BitVec.zero_xor, BitVec.xor_zero, env_key (by omega_arith), h.key hf (Nat.le_refl _),
      show 64 * 16 + (32 * (3 - q / 4) + 16 + q % 4) = 32 * (32 + (3 - q / 4)) + 16 + q % 4 by omega_arith,
      hw _ (by omega_arith) _ (by omega_arith), wl, Nat.mod_mod]
    exact pv_pl _
  obtain ⟨f, rfl⟩ := hsame
  have ha : addr B 8 = B.setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega_arith)
  have hwr : InRegions s.wr (addr B 8) 16 := ⟨_, by rw [h.wr]; exact hs.wr, by
    rw [ha]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine Wp.cons (s' := { s with xmm := f, mem := s.mem.writeW (addr B 8) (f .xmm2) }) ?_ (WP.block_nil ?_)
  · show State.store128 { s with xmm := f } (addr (s.gpr Impl.Modes.X86.sb) 8) _ = _
    rw [h.base, State.store128, ite_eq_left hwr]
  refine ⟨h.base, h.esp, h.rd, h.wr, h.syms, ?_, fun q hq => ?_⟩
  · show Frame _ s.mem (s.mem.writeW (addr B 8) _)
    rw [ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
  · show (s.mem.writeW (addr B 8) (f .xmm2)) _ = _
    rw [← ha, ← byte_readW (s.mem.writeW (addr B 8) (f .xmm2)) (addr B 8) (w := 128) (k := q) (by omega_arith),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact v q hq

/-- `crypt` enciphers the block at byte 8 of the scratch buffer, under the
round keys in the entries, and changes nothing else but the entries'
words. -/
theorem crypt_wp {k : Spec.Sm4.Schedule} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 306)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (k.getD i 0)) :
    WP isa crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 8, 16⟩, ⟨B.setWidth 64 + BitVec.ofNat 64 32, 1152⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (k.getD i 0)) ∧
      Spec.Aes.bytesAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 8) 16 =
        Spec.Sm4.cipher k (Spec.Aes.bytesAt s.mem (B.setWidth 64 + BitVec.ofNat 64 8) 16) := by
  have hf := hs.fit
  obtain ⟨rk, hrk⟩ : ∃ rk : Nat → Word, rk = fun i => k.getD i 0 := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk, blk = Spec.Sm4.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 8) := ⟨_, rfl⟩
  have hk' : ∀ i < 32, KeyAt s.mem B i (rk i) := by rw [hrk]; exact hk
  show WP isa (.seq (.block (cryptHead ++ cryptKey)) (.seq (.loop (.block turn) .ne) (.block cryptTail))) s _
  refine WP.seq (WP.mono (cryptHead_wp hB hs htab hk') fun s₁ ⟨a₁, m₁, c₁, f₁, k₁, w₁, x₁, y₁⟩ => ?_)
  have hI : Inv s B rk blk 16 s₁ := by
    refine ⟨Nat.le_refl _, a₁, m₁, c₁, f₁, k₁, bwd s.mem B 0, bwd s.mem B 1, bwd s.mem B 2, bwd s.mem B 3, ?_,
      w₁ 0 (by decide), w₁ 1 (by decide), w₁ 2 (by decide), w₁ 3 (by decide), x₁, fun _ => y₁⟩
    rw [hblk]; rfl
  refine WP.seq (WP.mono (loop_wp hs (by decide) hI) fun s₂ ⟨_, a₂, m₂, _, f₂, k₂, x0, x1, x2, x3, h32, v0, v1, v2, v3, _, _⟩ => ?_)
  have hw : ∀ w < 4, WordAt s₂.mem B (32 + w) ([x0, x1, x2, x3].getD w 0) := fun w hw4 => by
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw4]) with rfl | rfl | rfl | rfl
    · exact v0
    · exact v1
    · exact v2
    · exact v3
  refine WP.mono (cryptTail_wp hs a₂ m₂ hw) fun s₃ ⟨b₃, e₃, r₃, w₃, y₃, f₃, v₃⟩ => ⟨b₃, e₃, r₃, w₃, y₃, ?_, ?_, ?_⟩
  · exact (f₂.mono fun r hr => List.mem_cons_of_mem _ hr).trans (f₃.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)
  · intro i hi q hq
    have := f₃.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (32 + (32 * i + q)), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_using [hi, hq]) (by omega_arith))
      (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    have e := k₂ i hi q hq
    rw [hrk] at e
    rw [eAt, this]
    exact e
  · rw [Spec.Sm4.cipher, Proof.Sm4.bytesAt_eq_blockAt s.mem, Proof.Sm4.ofFn_toList, ← hblk, Spec.Sm4.encryptBlock, ← hrk]
    have hc : Spec.Sm4.crypt rk blk = Vector.ofFn fun i : Fin 16 =>
        byteAt ((#v[x3, x2, x1, x0] : Vector Word 4).getD (i.val / 4) 0) (i.val % 4) := by
      unfold Spec.Sm4.crypt
      rw [show (List.range 32).foldl (fun s i => Spec.Sm4.round (rk i) s) (Spec.Sm4.initial blk) = st rk blk 32 from rfl,
        show st rk blk 32 = (x0, x1, x2, x3) from h32]
      rfl
    rw [hc]
    refine List.ext_getElem (by simp [Spec.Aes.bytesAt]) fun q h₁ _ => ?_
    have hq : q < 16 := by simpa [Spec.Aes.bytesAt] using h₁
    rw [Vector.getElem_toList, Vector.getElem_ofFn]
    simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
    rw [v₃ q hq]
    rcases (show q / 4 = 0 ∨ q / 4 = 1 ∨ q / 4 = 2 ∨ q / 4 = 3 by omega_using [hq]) with h | h | h | h <;> rw [h] <;> rfl

end

/-! ## The round keys `prepare` leaves -/

section

open VG.Impl.Modes.X86 (at_ argOp)

/-- Round key `i` of the schedule at `p`. -/
def rkAt (m : Mem) (p : BitVec 32) (i : Nat) : Word := (Spec.Sm4.scheduleAt m (p.setWidth 64)).getD i 0

/-- The schedule's words are little-endian. -/
theorem byteAt_rkAt (m : Mem) (p : BitVec 32) {i k : Nat} (hi : i < 32) (hk : k < 4) :
    byteAt (rkAt m p i) k = m (p.setWidth 64 + BitVec.ofNat 64 (4 * i + (3 - k))) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_byteAt _ hk hj, rkAt,
    show (Spec.Sm4.scheduleAt m (p.setWidth 64)).getD i 0 = (Spec.Sm4.scheduleAt m (p.setWidth 64))[i]'hi by
      simp [Vector.getD, hi],
    Proof.Sm4.getLsbD_scheduleAt m _ hi (by omega_arith) hj]

/-- The schedule's bytes in `m` are those of `M`. -/
def Sch (M m : Mem) (p : BitVec 32) : Prop :=
  ∀ o < 128, m (p.setWidth 64 + BitVec.ofNat 64 o) = M (p.setWidth 64 + BitVec.ofNat 64 o)

/-- What `prepare` needs of the state it starts in: the scratch buffer, and
the schedule, apart from it. -/
structure PEnv (s₀ : State) (B p : BitVec 32) : Prop where
  scr : ScrIn s₀ B 306
  sch : (⟨p.setWidth 64, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr
  pfit : p.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨p.setWidth 64, 128⟩ ⟨B.setWidth 64, 1224⟩

/-- A state of `prepare` after `i` groups of four round keys: the
schedule's pointer, the entries' pointer, the table's address, and the
mask. -/
structure PAt (s₀ : State) (B p : BitVec 32) (i : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  sp : s.gpr .eax = p + BitVec.ofNat 32 (16 * i)
  kp : s.gpr kr = B + BitVec.ofNat 32 (32 + 128 * i)
  msk : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8

variable {s₀ s : State} {B p : BitVec 32} {i : Nat} {M : Mem}

theorem PAt.kr64 (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (32 + 128 * i) := by
  have hf := he.scr.fit
  rw [h.kp]; exact addr_eq (by omega_arith)

theorem PAt.krNat (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).toNat = B.toNat + (32 + 128 * i) := by
  have hf := he.scr.fit
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 32 + 128 * i) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem PAt.ax64 (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
  have hf := he.pfit
  rw [h.sp]; exact addr_eq (by omega_arith)

theorem PAt.axNat (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).toNat = p.toNat + 16 * i := by
  have hf := he.pfit
  rw [h.sp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- Four round keys of the schedule to their entries (`prepGroupX`). -/
theorem prepGroupX_wp (he : PEnv s₀ B p) (hi : i < 8) (h : PAt s₀ B p i s) (hS : Sch M s.mem p) :
    WP isa (.block prepGroupX) s fun s' => PAt s₀ B p i s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 128 * i), 112⟩] s.mem s'.mem ∧
      ∀ w < 4, KeyAt s'.mem B (4 * i + w) (rkAt M p (4 * i + w)) := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have hk := h.krNat he hi
  have ha := h.axNat he hi
  have rel : Rel pparams (envOf pparams s) regs₀ s :=
    (rel_init (p := pparams) (by show s.gpr tbr = s.syms tableName; rw [h.tb, h.syms])
      (by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith)
      fun o ho => ⟨_, by rw [h.rd, h.wr]; exact he.sch, by
        show Region.Contains _ (addr (s.gpr .eax) o) 16
        have ho' : o + 16 ≤ 16 := ho
        rw [addr_eq (by omega_arith), h.ax64 he hi, Offset.add_ofNat_add_ofNat]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩).const m0 h.msk
  have ok : OutOk pparams poparams s := by
    refine ⟨by show (s.gpr kr).toNat + 112 ≤ _; omega_arith, fun o ho => ⟨_, by rw [h.wr]; exact he.scr.wr, ?_⟩, ?_,
      by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith⟩
    · show Region.Contains _ (addr (s.gpr kr) o) 16
      have ho' : o + 16 ≤ 112 := ho
      rw [addr_eq (by omega_arith), h.kr64 he hi, Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · show Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 16⟩ ⟨(s.gpr kr).setWidth 64, 112⟩
      rw [h.ax64 he hi, h.kr64 he hi]
      exact (he.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  have hok := prep_all.1
  unfold prepGroupOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, oin⟩, cm⟩ := hok
  refine runS_wp ok (RelS.init rel rfl) hrun fun s' hr => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at cm
  have st : ∀ {w : Nat}, outOk σ.2 (32 * w) (pw w) = true → w < 4 → KeyAt s'.mem B (4 * i + w) (rkAt M p (4 * i + w)) :=
    fun {w} ho hw4 q hq => by
    have h4 : q % 4 < 4 := Nat.mod_lt _ (by decide)
    have := hr.out ho hq
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, Offset.add_ofNat_add_ofNat] at this
    rw [eAt, show 32 + (32 * (4 * i + w) + q) = 32 + 128 * i + (32 * w + q) by omega_arith, this, pw, BV.eval, mask_zero,
      cterms_sum, BitVec.zero_xor, BitVec.xor_zero, kv,
      mask_bit _ (by show 128 + (4 * w + (3 - q % 4)) < 1024; omega_using [hw4]), envOf_key,
      show (s.gpr pparams.kreg) = s.gpr .eax from rfl, h.ax64 he hi, Offset.add_ofNat_add_ofNat,
      hS _ (by omega_using [hi, hw4]), wk, byteAt_rkAt _ _ (by omega_using [hi, hw4]) h4]
    rw [show 16 * i + (4 * w + (3 - q % 4)) = 4 * (4 * i + w) + (3 - q % 4) by omega_arith]
    rfl
  refine ⟨⟨by rw [hr.gpr]; exact h.base, by rw [hr.gpr]; exact h.esp, hr.rd.trans h.rd, hr.wr.trans h.wr,
    hr.syms.trans h.syms, by rw [hr.gpr]; exact h.tb, by rw [hr.gpr]; exact h.sp, by rw [hr.gpr]; exact h.kp,
    fun q hq => by
      rw [hr.rel.bytes cm.1 q hq, BV.same_eval _ (List.all_eq_true.mp cm.2 q (List.mem_range.mpr hq)), BV.cst_eval]⟩,
    by rw [hr.gpr], ?_, fun w hw4 => ?_⟩
  · have := hr.frameIn oin
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, BitVec.add_zero, Nat.sub_zero] at this
    exact this
  · rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw4]) with rfl | rfl | rfl | rfl
    · exact st o0 (by decide)
    · exact st o1 (by decide)
    · exact st o2 (by decide)
    · exact st o3 (by decide)

/-- The schedule is outside what `prepare` writes. -/
theorem Sch.frame {m m' : Mem} {a n : Nat} (h : Sch M m p) (he : PEnv s₀ B p)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩] m m') (han : a + n ≤ 1224) : Sch M m' p := fun o ho => by
  rw [← h o ho]
  refine hf.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => ?_) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  rw [List.mem_singleton] at hr; subst hr
  exact he.sep.sub_right (Offset.sub_base _ han)

/-- The loop's invariant, with `n` groups left, from the memory `m₁`. -/
def PInv (s₀ : State) (M m₁ : Mem) (B p : BitVec 32) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ PAt s₀ B p (8 - n) s ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ Sch M s.mem p ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 1152⟩] m₁ s.mem ∧
    ∀ j < 4 * (8 - n), KeyAt s.mem B j (rkAt M p j)

theorem pturn_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv s₀ M m₁ B p n s) :
    WP isa (.block prepGroup) s fun s' => s'.zf = some (decide (n = 1)) ∧ PInv s₀ M m₁ B p (n - 1) s' := by
  obtain ⟨hn8, a, hc, hS, hF, K⟩ := hI
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a K
  have hm8 : m < 8 := by omega_using [hn, hm']
  have hf := he.scr.fit
  refine WP.block_append_iff.mpr (WP.mono (prepGroupX_wp he hm8 a hS) fun s₁ ⟨a₁, c₁, f₁, k₁⟩ => ?_)
  show WP isa (.block [.alu .add .eax (.imm 16), .alu .add kr (.imm 128), .alu .sub .ecx (.imm 1)]) s₁ _
  refine wp_addi_x fun s₂ u₂ x₂ => wp_addi_x fun s₃ u₃ x₃ => wp_subi_x fun s₄ u₄ x₄ z₄ => WP.block_nil ?_
  have e₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have c₃ : s₃.gpr .ecx = BitVec.ofNat 32 n := by rw [u₃.other _ (by decide), u₂.other _ (by decide), c₁, hc]
  refine ⟨?_, by omega_using [hn8], ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [z₄, c₃, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [show 8 - (n - 1) = m + 1 by omega_using [hn, hm', hn8]]
    refine ⟨?_, ?_, by rw [u₄.rd, u₃.rd, u₂.rd]; exact a₁.rd, by rw [u₄.wr, u₃.wr, u₂.wr]; exact a₁.wr,
      by rw [u₄.syms, u₃.syms, u₂.syms]; exact a₁.syms, ?_, ?_, ?_, by rw [x₄, x₃, x₂]; exact a₁.msk⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact a₁.base
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact a₁.esp
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact a₁.tb
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, a₁.sp,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_ofNat_add_ofNat]
      congr 2
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), a₁.kp,
        show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, Offset.add_ofNat_add_ofNat]
      congr 2
  · rw [u₄.gpr, c₃]; exact Wp.ofNat_pred hn
  · rw [e₄]
    exact hS.frame he f₁ (by omega_using [hm8])
  · rw [e₄]
    refine hF.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton.mp hr]
    exact Offset.sub _ (by omega_arith) (by omega_using [hm8])
  · rw [e₄]
    by_cases hj' : j < 4 * m
    · intro q hq
      have := f₁.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (32 + (32 * j + q)), 1⟩) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_using [hj', hq])) (by omega_using [hj', hq, hm8])
          (by omega_using [hm8])) (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
      rw [BitVec.add_zero] at this
      rw [eAt, this]
      exact K j hj' q hq
    · have := k₁ (j - 4 * m) (by omega_using [hj, hj', hn, hm', hn8])
      rwa [show 4 * m + (j - 4 * m) = j by omega_using [hj']] at this

/-- The eight groups: the 32 round keys in their entries. -/
theorem ploop_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv s₀ M m₁ B p n s) :
    WP isa (.loop (.block prepGroup) .ne) s (PInv s₀ M m₁ B p 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ PInv s₀ M m₁ B p n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (pturn_wp he hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

/-- The table's address to the scratch buffer's first slot, the registers
of the loop, and the mask (`prepHead`), with the table's address in `eax`. -/
theorem prepHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hax : s.gpr .eax = s.syms tableName)
    (hS : Sch M s.mem p) (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4)
    (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 1224⟩) :
    WP isa (.block prepHead) s fun s' => PAt s B p 0 s' ∧ s'.gpr .ecx = BitVec.ofNat 32 8 ∧ Sch M s'.mem p ∧
      Frame [⟨B.setWidth 64, 4⟩] s.mem s'.mem ∧ s'.mem.readW (B.setWidth 64) 32 = s.syms tableName := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have ha0 : addr B 0 = B.setWidth 64 := by rw [addr_eq (by omega_arith), BitVec.add_zero]
  have hw : InRegions s.wr (addr B 0) 4 := ⟨_, he.scr.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.store ⟨Impl.Modes.X86.sb, 0⟩ .eax :: .mov tbr (.reg .eax) ::
    .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) :: .alu .add kr (.imm 32) ::
    .mov .ecx (.imm 8) :: [tb m0 oM0])) s _
  refine Wp.wp_stm hB hw fun s₂ u₂ => ?_
  have f₂ : Frame [⟨B.setWidth 64, 4⟩] s.mem s₂.mem := by
    rw [u₂.mem, ha0]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have sub4 : Region.Sub ⟨B.setWidth 64, 4⟩ ⟨B.setWidth 64, 1224⟩ := Region.sub_prefix (by decide)
  have e0 : s₂.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [f₂.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0B.sub_right sub4) (by decide), hp]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [u₃.other _ (by decide), u₂.gpr]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin0)
    fun s₄ u₄ => ?_
  refine Wp.wp_mov fun s₅ u₅ => ?_
  refine Wp.wp_addi fun s₆ u₆ => ?_
  refine Wp.wp_movi fun s₇ u₇ => ?_
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have r₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]
  have w₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]
  have y₇ : s₇.syms = s.syms := by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms]
  have b₇ : s₇.gpr Impl.Modes.X86.sb = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, hB]
  have sp₇ : s₇.gpr .esp = s.gpr .esp := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]
  have t₇ : s₇.gpr tbr = s.syms tableName := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.gpr, hax]
  have a₇ : s₇.gpr .eax = p := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem]
    exact e0
  have c₇ : s₇.gpr .ecx = BitVec.ofNat 32 8 := by rw [u₇.gpr]; rfl
  have k₇ : s₇.gpr kr = B + BitVec.ofNat 32 (32 + 128 * 0) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hB]
    rfl
  have hS₇ : Sch M s₇.mem p := by
    rw [m₇]
    exact hS.frame (a := 0) he (by rw [BitVec.add_zero]; exact f₂) (by decide)
  have hok := prep_all.2
  unfold prepMaskOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  have hrel : Rel pparams (envOf pparams s₇) Regs.init s₇ := rel_init (p := pparams)
    (by show s₇.gpr tbr = s₇.syms tableName; rw [t₇, y₇]) (by show (s₇.gpr .eax).toNat + 16 ≤ _; rw [a₇]; omega_arith)
    fun o ho => ⟨_, by rw [r₇, w₇]; exact he.sch, by
      show Region.Contains _ (addr (s₇.gpr .eax) o) 16
      have ho' : o + 16 ≤ 16 := ho
      rw [a₇, addr_eq (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine run_wp hrel hrun fun s' hr hs => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
  have hm : ∀ q < 16, byte (s'.xmm m0) q = 0x0f#8 := fun q hq => by
    rw [hr.bytes hok.1 q hq, BV.same_eval _ (List.all_eq_true.mp hok.2 q (List.mem_range.mpr hq)), BV.cst_eval]
  obtain ⟨f, rfl⟩ := hs
  refine ⟨⟨b₇, sp₇, r₇, w₇, y₇, t₇, by rw [show (_ : State).gpr .eax = s₇.gpr .eax from rfl, a₇]; simp, k₇, hm⟩,
    c₇, hS₇, by rw [show (_ : State).mem = s₇.mem from rfl, m₇]; exact f₂, ?_⟩
  show s₇.mem.readW (B.setWidth 64) 32 = _
  rw [m₇, u₂.mem, ha0, Mem.readW_writeW_self32, hax]

/-- `prepare` leaves the round keys of the schedule in the entries, and the
table's address in the scratch buffer's first slot; it writes only the
core's slots, and the four bytes below `esp` of the frame that gets the
table's address. -/
theorem prepare_wp (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hesp : 4 ≤ (s.gpr .esp).toNat)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 1224⟩)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 128⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩) :
    WP isa prepare s fun s' => (∀ i < 32, KeyAt s'.mem B i (rkAt s.mem p i)) ∧
      s'.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 1184⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
  have hf := he.scr.fit
  show WP isa (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block prepHead)
    (.loop (.block prepGroup) .ne))) s _
  refine WP.seq (WP.mono (symFrame_ok tableName s hesp) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  have ea₁ : ∀ k, s₁.ea (argOp k) = s.ea (argOp k) := fun k => by
    show addr (s₁.gpr .esp) _ = addr (s.gpr .esp) _
    rw [esp₁]
  have he₁ : PEnv s₁ B p :=
    ⟨⟨by rw [a₁.wr]; exact he.scr.wr, he.scr.fit⟩, by rw [a₁.rd, a₁.wr]; exact he.sch, he.pfit, he.sep⟩
  have hS₁ : Sch s.mem s₁.mem p := fun o ho =>
    a₁.frame.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hkS.symm) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  have p₁ : s₁.mem.readW (s.ea (argOp 0)) 32 = p := by
    rw [a₁.frame.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact h0S.symm) (by decide), hp]
  refine WP.seq (WP.mono (prepHead_wp (M := s.mem) (by rw [a₁.gpr _ (by decide)]; exact hB) he₁
    (by rw [a₁.addr, a₁.syms]) hS₁ (by rw [ea₁, a₁.rd, a₁.wr]; exact hin0) (by rw [ea₁]; exact p₁)
    (by rw [ea₁]; exact h0B)) fun s₂ ⟨a₂, c₂, hS₂, f₂, t₂⟩ => ?_)
  have hI : PInv s₁ s.mem s₂.mem B p 8 s₂ :=
    ⟨Nat.le_refl _, a₂, c₂, hS₂, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  refine WP.mono (ploop_wp he₁ (by decide) hI) fun s₃ ⟨_, a₃, _, _, F₃, K₃⟩ => ?_
  refine ⟨K₃, ?_, a₃.base, a₃.esp.trans esp₁, a₃.rd.trans a₁.rd, a₃.wr.trans a₁.wr, a₃.syms.trans a₁.syms, ?_⟩
  · rw [F₃.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), t₂, a₁.syms]
  · refine ((a₁.frame.mono fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (F₃.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩

end

/-! ## The core -/

section

open VG.Impl.Modes.X86 (at_ argOp)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout)

/-- The schedule, at the address in the first stack argument, outside the
regions `rs`, as is that argument, and the four bytes below `esp` apart
from both. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    k = Spec.Sm4.scheduleAt s.mem (p.setWidth 64) ∧ (⟨p.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr ∧
    p.toNat + 128 ≤ 2 ^ 32 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 128⟩ r) ∧
    (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨p.setWidth 64, 128⟩ ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩

theorem ea_esp {s s' : State} (h : s'.gpr .esp = s.gpr .esp) (i : Nat) : s'.ea (argOp i) = s.ea (argOp i) := by
  show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64
  rw [h]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin0, hp, hk, hsch, hfit, hdis, hd0, hkS, h0S⟩ := h
  have hea := ea_esp hesp
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin0, ?_, ?_, by rw [hrd, hwr]; exact hsch, hfit, hdis,
    by rw [hea]; exact hd0, by rw [hesp]; exact hkS, by rw [hesp, hea]; exact h0S⟩
  · rw [hea, hf.readW (Region.contains_self _ _) hd0 (by decide), hp]
  · rw [hk]
    exact (Proof.Sm4.scheduleAt_congr fun _ hi =>
      hf.bytes (R := ⟨p.setWidth 64, 128⟩) hdis (show (128 : Nat) ≤ 2 ^ 64 by decide) hi).symm

/-- The key `k` is ready in the scratch buffer at `B`: its round keys in
the entries, and the table's address in the first slot. -/
def Ready (s : State) (B : BitVec 32) (k : Spec.Sm4.Schedule) : Prop :=
  (∀ i < 32, KeyAt s.mem B i (k.getD i 0)) ∧ s.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧
    B.toNat + 1224 ≤ 2 ^ 32

theorem core_slots : core.slots = 296 := rfl

/-- The key stays ready through what a mode writes outside the core's slots
or within its buffer. -/
theorem ready_frame {s s' : State} {B : BitVec 32} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : Ready s B k) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion core B) r ∨ Region.Sub r (blkRegion core B)) : Ready s' B k := by
  obtain ⟨hk, ht, hfit⟩ := h
  have keep : ∀ {a n : Nat}, a + n ≤ 1184 → (a + n ≤ 8 ∨ 24 ≤ a) → ∀ r ∈ rs,
      Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r := fun {a n} h₁ h₂ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by rw [core_slots]; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * core.buf) (k := 4 * core.bw * core.G)
        (by show a + n ≤ 8 ∨ 8 + 16 ≤ a; omega_arith) (by omega_arith) (by decide)).sub_right h
  refine ⟨fun i hi q hq => ?_, ?_, hfit⟩
  · have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (32 + (32 * i + q)), 1⟩)
      (keep (by omega_arith) (.inr (by omega_arith))) (by show (1 : Nat) ≤ 2 ^ 64; decide) (i := 0)
      (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    rw [eAt, this]
    exact hk i hi q hq
  · have e := hf.readW (r := ⟨B.setWidth 64 + BitVec.ofNat 64 0, 4⟩) (a := B.setWidth 64 + BitVec.ofNat 64 0)
      (w := 32) (Region.contains_self _ 4) (keep (by decide) (.inl (by decide))) (by decide)
    rw [BitVec.add_zero] at e
    rw [e, hsy]; exact ht

theorem prepare_ok {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.Sm4.Schedule}
    (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B core.total)
    (hR : (⟨B.setWidth 64, 4 * core.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (hsp : core.stack ≤ (s.gpr .esp).toNat) :
    WP isa core.prepare s fun s' => Ready s' B k ∧ s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin0, hp, hk, hsch, hfit, hdis, hd0, hkS, h0S⟩ := hk
  have he : PEnv s B p := ⟨hs, hsch, hfit, hdis _ hR⟩
  refine WP.mono (prepare_wp hB he hsp hin0 hp (hd0 _ hR) hkS h0S) fun s' ⟨K, t, b, e, rd, wr, sy, f⟩ => ?_
  refine ⟨⟨fun i hi => ?_, by rw [t, sy], hs.fit⟩, b, e, f, rd, wr⟩
  rw [hk]
  exact K i hi

theorem crypt_ok {s : State} {B : BitVec 32} {k : Spec.Sm4.Schedule} (hB : s.gpr Impl.Modes.X86.sb = B)
    (hs : ScrIn s B core.total) (hr : Ready s B k) :
    WP isa core.crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready s' B k ∧
      Frame [coreRegion core B, stkRegion (s.gpr .esp) core.stack] s.mem s'.mem ∧
      (∀ j < core.G, Spec.Aes.bytesAt s'.mem (blkAddr core B j) (4 * core.bw) =
        Spec.Sm4.cipher k (Spec.Aes.bytesAt s.mem (blkAddr core B j) (4 * core.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, ht, hfit⟩ := hr
  refine WP.mono (crypt_wp hB hs ht hk) fun s' ⟨b, e, rd, wr, sy, f, k', v⟩ => ?_
  have hblk : blkAddr core B 0 = B.setWidth 64 + BitVec.ofNat 64 8 := by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 2) + BitVec.ofNat 64 (4 * 4 * 0) = _
    rw [Offset.add_ofNat_add_ofNat]
  refine ⟨b, e, ⟨k', ?_, hfit⟩, f.sub fun r hr => ?_, fun j hj => ?_, rd, wr⟩
  · rw [f.readW (r := ⟨B.setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.base_disjoint _ (by decide) (by decide)
      · exact Offset.base_disjoint _ (by decide) (by decide)) (by decide), sy]
    exact ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
  · have h0 : j = 0 := by
      have : j < 1 := hj
      omega_arith
    subst h0
    rw [hblk]
    exact v

/-- SM4's core by the AES S-box meets what the modes need. -/
def coreSpec : CoreSpec core where
  Key := Spec.Sm4.Schedule
  cipher k := Spec.Sm4.cipher k
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by simp [Spec.Sm4.cipher, core]
  layout := ⟨by decide, .inr rfl, by decide, by decide⟩
  keyArgs_congr h e r w _ f := keyArgs_congr h e r w f
  ready_frame h _ _ _ sy f _ hd := ready_frame h sy f hd
  prepare_wp hB hs hR hk hsp := prepare_ok hB hs hR hk hsp
  crypt_wp hB hs hr _ := crypt_ok hB hs hr

end

end VG.Proof.Sm4.X86.AesNi
