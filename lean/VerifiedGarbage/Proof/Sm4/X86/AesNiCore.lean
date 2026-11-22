module

public import VerifiedGarbage.Proof.Sm4.X86.AesNiMaps
public import VerifiedGarbage.Proof.Sm4.Bitsliced
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Modes.X86.Core
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
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

/-- Byte `o` of the scratch buffer at `edi`. -/
def kb (s : State) (o : Nat) : Byte := s.mem ((s.gpr Impl.Modes.X86.sb).setWidth 64 + BitVec.ofNat 64 o)

/-- What a round needs of the state: the table's address in its register,
the scratch buffer's first 96 bytes, which end with the ring, readable, and
the mask. -/
structure Env (s : State) : Prop where
  tb : s.gpr tbr = s.syms tableName
  fit : (s.gpr Impl.Modes.X86.sb).toNat + 96 ≤ 2 ^ 32
  acc : ∀ o, o + 16 ≤ 96 → InRegions (s.rd ++ s.wr) (addr (s.gpr Impl.Modes.X86.sb) o) 16
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

theorem env_key {o : Nat} (ho : o < 96) : mask (envOf params s) (kv o) nvars = kb s o := by
  rw [kv, mask_bit _ (by show 128 + o < 1024; omega_using [ho]), envOf_key]; rfl

theorem aT_sum (env : Nat → BitVec 8) (t : Nat) (a : XReg) (p : Nat) :
    sum env (aT t a p) = am t (aesSbox (mask env (var a (srow p)) nvars)) := by
  simp only [aT, sum, BitVec.xor_zero]; rfl

theorem sigma_sum (a : XReg) (q : Nat) :
    sum (envOf params s) (sigma a q) = sig (fun p => byte (s.xmm a) p) q := by
  simp only [sigma, sum_append, aT_sum, sig, env_var a (srow_lt _)]

/-- A round but its key's load and its word's store: what it leaves in `c`
and in `e`, of the bytes it starts with. -/
theorem roundX_wp {a c n e : XReg} {s0 s2 : Nat} (hok : roundOk a c n e s0 s2 = true) (h0 : s0 + 16 ≤ 96)
    (h2 : s2 + 16 ≤ 96) (he : Env s) :
    WP isa (.block (roundX a c n e s0 s2)) s fun s' =>
      Same s s' ∧
      (∀ q < 16, byte (s'.xmm c) q = kb s (s0 + q) ^^^ byte (s.xmm e) q ^^^ kb s (s2 + q) ^^^
        byte (s.xmm n) q ^^^ sig (fun p => byte (s.xmm a) p) q) ∧
      (∀ q < 16, byte (s'.xmm e) q = kb s (s0 + q) ^^^ sig (fun p => byte (s.xmm a) p) q) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  unfold roundOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hc, hes⟩, cc⟩, ce⟩, cm⟩ := hok
  refine run_wp he.rel hrun fun s' hr hsame => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at cm
  refine ⟨hsame, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [hr.bytes hc q hq, BV.same_eval _ (List.all_eq_true.mp cc q (List.mem_range.mpr hq))]
    simp only [BV.eval, mask_xor, sigma_sum, BitVec.xor_zero, env_key (show s0 + q < 96 by omega_using [h0, hq]),
      env_key (show s2 + q < 96 by omega_using [h2, hq]), env_var n hq, env_var e hq]
  · rw [hr.bytes hes q hq, BV.same_eval _ (List.all_eq_true.mp ce q (List.mem_range.mpr hq))]
    simp only [BV.eval, sigma_sum, BitVec.xor_zero, env_key (show s0 + q < 96 by omega_using [h0, hq])]
  · rw [hr.bytes cm.1 q hq, BV.same_eval _ (List.all_eq_true.mp cm.2 q (List.mem_range.mpr hq)), BV.cst_eval]

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

/-! ## The ring and the round keys in the scratch buffer -/

/-- Byte `o` of the scratch buffer at `B`. -/
def sAt (m : Mem) (B : BitVec 32) (o : Nat) : Byte := m (B.setWidth 64 + BitVec.ofNat 64 o)

/-- The place of round key `i` holds `k`; the ring's place `j` holds the word `X`. -/
def KeyAt (m : Mem) (B : BitVec 32) (i : Nat) (k : Word) : Prop := ∀ q < 16, sAt m B (96 + 16 * i + q) = wk k q
def WordAt (m : Mem) (B : BitVec 32) (j : Nat) (X : Word) : Prop := ∀ q < 16, sAt m B (32 + 16 * j + q) = wl X q

/-- A byte of the scratch buffer outside the bytes of several stores. -/
theorem frame_sAt_list {m m' : Mem} {B : BitVec 32} {los : List Nat} {o : Nat}
    (hf : Frame (los.map fun lo => (⟨B.setWidth 64 + BitVec.ofNat 64 lo, 16⟩ : Region)) m m')
    (ho : ∀ lo ∈ los, o < lo ∨ lo + 16 ≤ o) (hb : o < 2 ^ 32) (hl : ∀ lo ∈ los, lo < 2 ^ 32) :
    sAt m' B o = sAt m B o := by
  have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 o, 1⟩) (fun r hr => by
    obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hr
    exact Offset.disjoint _ (by omega_using [ho lo hlo]) (by omega_using [hb]) (by omega_using [hl lo hlo]))
    (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
  rw [BitVec.add_zero] at this
  exact this

/-- A byte of the scratch buffer outside the 16 bytes of a store. -/
theorem frame_sAt {m m' : Mem} {B : BitVec 32} {lo o : Nat}
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 lo, 16⟩] m m') (ho : o < lo ∨ lo + 16 ≤ o)
    (hb : o < 2 ^ 32) (hl : lo < 2 ^ 32) : sAt m' B o = sAt m B o :=
  frame_sAt_list (los := [lo]) hf (fun _ h => by rw [List.mem_singleton.mp h]; exact ho) hb
    (fun _ h => by rw [List.mem_singleton.mp h]; exact hl)

theorem KeyAt.frame {m m' : Mem} {B : BitVec 32} {i j : Nat} {k : Word} (h : KeyAt m B i k)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j), 16⟩] m m') (hi : i < 33) (hj : j < 4) :
    KeyAt m' B i k := fun q hq => by
  rw [frame_sAt hf (by omega_using [hq, hj]) (by omega_using [hi, hq]) (by omega_using [hj])]; exact h q hq

theorem WordAt.frame {m m' : Mem} {B : BitVec 32} {i j : Nat} {X : Word} (h : WordAt m B i X)
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j), 16⟩] m m') (hi : i < 4) (hj : j < 4)
    (hne : i ≠ j) : WordAt m' B i X := fun q hq => by
  rw [frame_sAt hf (by omega_using [hq, hne]) (by omega_using [hi, hq]) (by omega_using [hj])]; exact h q hq

/-- The ring's places are in the ring. -/
theorem ring_sub (B : BitVec 32) {j : Nat} (hj : j < 4) :
    Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j), 16⟩ ⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩ :=
  Offset.sub _ (by omega_arith) (by omega_using [hj])

/-- A state of `crypt` after `n` turns, from the state `s₀` it starts in:
the scratch buffer's address, the round keys' pointer, and the table's
address. -/
structure At (s₀ : State) (B : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  kp : s.gpr kr = B + BitVec.ofNat 32 (96 + 64 * n)

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

/-- `movdqu d, [b + o]`, of readable bytes. -/
theorem wp_ldx {d : XReg} {b : Reg} {o : Nat} (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 16)
    (k : WP isa (.block is) (s.setXmm d (s.mem.readW (addr (s.gpr b) o) 128)) Q) :
    WP isa (.block (.movdquLoad d ⟨b, o⟩ :: is)) s Q := by
  refine Wp.cons (s' := s.setXmm d (s.mem.readW (addr (s.gpr b) o) 128)) ?_ k
  show (s.load128 (addr (s.gpr b) o)).map _ = _
  rw [State.load128, ite_eq_left hin]; rfl

/-- `movdqu [b + o], r`, to writable bytes. -/
theorem wp_stx {b : Reg} {o : Nat} {r : XReg} (hin : InRegions s.wr (addr (s.gpr b) o) 16)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.xmm r) } Q) :
    WP isa (.block (.movdquStore ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.xmm r) }) ?_ k
  show State.store128 s (addr (s.gpr b) o) _ = _
  rw [State.store128, ite_eq_left hin]

end

section
variable {s₀ s : State} {B : BitVec 32} {n : Nat}

theorem At.of_gpr {s' : State} (h : At s₀ B n s) (hg : s'.gpr = s.gpr) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsy : s'.syms = s.syms) : At s₀ B n s' :=
  ⟨by rw [hg]; exact h.base, by rw [hg]; exact h.esp, hrd.trans h.rd, hwr.trans h.wr, hsy.trans h.syms,
    by rw [hg]; exact h.tb, by rw [hg]; exact h.kp⟩

theorem At.kr64 (h : At s₀ B n s) (hf : B.toNat + 664 ≤ 2 ^ 32) (hn : n ≤ 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (96 + 64 * n) := by
  rw [h.kp]; exact addr_eq (by omega_using [hf, hn])

theorem At.krNat (h : At s₀ B n s) (hf : B.toNat + 664 ≤ 2 ^ 32) (hn : n ≤ 8) :
    (s.gpr kr).toNat = B.toNat + (96 + 64 * n) := by
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 96 + 64 * n) (by omega_using [hn]),
    Nat.mod_eq_of_lt (by omega_using [hf, hn])]

theorem At.scr (h : At s₀ B n s) (o : Nat) : kb s o = sAt s.mem B o := by
  rw [kb, h.base]; rfl

theorem At.env (h : At s₀ B n s) (hs : ScrIn s₀ B 166) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) : Env s := by
  have hf : B.toNat + 664 ≤ 2 ^ 32 := hs.fit
  refine ⟨by rw [h.tb, h.syms], by rw [h.base]; omega_using [hf],
    fun o ho => ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), ?_⟩, hm⟩
  rw [h.base, addr_eq (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- Round `j` of turn `n`: round `4 n + j` of the block. -/
theorem round_ok {a c nr e : XReg} {j : Nat}
    (hok : roundOk a c nr e (oR + 16 * j) (oR + 16 * ((j + 2) % 4)) = true) (hj : j < 4) (hea : ¬a = e)
    (hen : ¬nr = e) (hem : ¬m0 = e) (hs : ScrIn s₀ B 166) (hn : n < 8) (h : At s₀ B n s)
    (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8) {x0 x1 x2 x3 k : Word}
    (hin : Hk (s.xmm a) (x1 ^^^ x2 ^^^ x3 ^^^ k)) (hx3 : Hw (s.xmm nr) x3)
    (w0 : WordAt s.mem B j x0) (w2 : WordAt s.mem B ((j + 2) % 4) x2) :
    WP isa (.block (round a c nr e j)) s fun s' =>
      At s₀ B n s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr = s.gpr ∧ s'.zf = s.zf ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j), 16⟩] s.mem s'.mem ∧
      Hw (s'.xmm e) (x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) ∧
      WordAt s'.mem B j (x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) ∧
      ∀ k', KeyAt s.mem B (4 * n + j + 1) k' →
        Hk (s'.xmm c) (x2 ^^^ x3 ^^^ (x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) ^^^ k') := by
  have hf : B.toNat + 664 ≤ 2 ^ 32 := hs.fit
  have hle := Nat.le_of_lt hn
  have hkn := h.krNat hf hle
  show WP isa (.block (.movdquLoad e ⟨kr, 16 * j + 16⟩ ::
    (roundX a c nr e (oR + 16 * j) (oR + 16 * ((j + 2) % 4)) ++
      [.movdquStore ⟨Impl.Modes.X86.sb, 32 + 16 * j⟩ e]))) s _
  -- the next round's key
  have hl : InRegions (s.rd ++ s.wr) (addr (s.gpr kr) (16 * j + 16)) 16 :=
    ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hs.wr), by
      rw [addr_eq (by omega_using [hkn, hf, hn, hj]), h.kr64 hf hle, Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_using [hn, hj]) (by omega_using [hn, hj])⟩
  refine wp_ldx hl ?_
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = s.setXmm e (s.mem.readW (addr (s.gpr kr) (16 * j + 16)) 128) := ⟨_, rfl⟩
  rw [← hs₁]
  have a₁ : At s₀ B n s₁ := by subst hs₁; exact h.of_gpr rfl rfl rfl rfl
  have g₁ : s₁.gpr = s.gpr := by subst hs₁; rfl
  have z₁ : s₁.zf = s.zf := by subst hs₁; rfl
  have m₁ : s₁.mem = s.mem := by subst hs₁; rfl
  have xa : s₁.xmm a = s.xmm a := by subst hs₁; exact RegUpd.xmm_setXmm_of_ne _ _ hea
  have xn : s₁.xmm nr = s.xmm nr := by subst hs₁; exact RegUpd.xmm_setXmm_of_ne _ _ hen
  have xm : s₁.xmm m0 = s.xmm m0 := by subst hs₁; exact RegUpd.xmm_setXmm_of_ne _ _ hem
  have ke : ∀ q < 16, byte (s₁.xmm e) q = sAt s.mem B (96 + 16 * (4 * n + j + 1) + q) := fun q hq => by
    subst hs₁
    rw [RegUpd.xmm_setXmm_self]
    show (s.mem.readW (addr (s.gpr kr) (16 * j + 16)) 128).extractLsb' (8 * q) 8 = _
    rw [byte_readW _ _ (by omega_using [hq]), addr_eq (by omega_using [hkn, hf, hn, hj]), h.kr64 hf hle,
      Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat, sAt,
      show 96 + 16 * (4 * n + j + 1) + q = 96 + 64 * n + (16 * j + 16 + q) by omega_arith]
  have s0le : oR + 16 * j + 16 ≤ 96 := by show 32 + 16 * j + 16 ≤ 96; omega_using [hj]
  have s2le : oR + 16 * ((j + 2) % 4) + 16 ≤ 96 := by show 32 + 16 * ((j + 2) % 4) + 16 ≤ 96; omega_arith
  refine WP.block_append_iff.mpr (WP.mono (roundX_wp hok s0le s2le
    (a₁.env hs fun q hq => by rw [xm]; exact hm q hq)) fun s₂ ⟨hsame, bc, be, bm⟩ => ?_)
  have sg : ∀ q, sig (fun p => byte (s₁.xmm a) p) q = wl (Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) q := fun q =>
    sig_eq (fun p hp => by rw [xa]; exact hin p hp) q
  have e0 : ∀ q < 16, kb s₁ (oR + 16 * j + q) = wl x0 q := fun q hq => by rw [a₁.scr, m₁]; exact w0 q hq
  have e2 : ∀ q < 16, kb s₁ (oR + 16 * ((j + 2) % 4) + q) = wl x2 q := fun q hq => by
    rw [a₁.scr, m₁]; exact w2 q hq
  obtain ⟨f, rfl⟩ := hsame
  have ev : ∀ q < 16, byte (f e) q = wl (x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ k)) q := fun q hq =>
    (be q hq).trans (by rw [e0 q hq, sg, wl_xor])
  -- the new word to its place
  have ha : addr B (32 + 16 * j) = B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j) :=
    addr_eq (by omega_using [hf, hj])
  have hwr : InRegions s₁.wr (addr (s₁.gpr Impl.Modes.X86.sb) (32 + 16 * j)) 16 :=
    ⟨_, by rw [a₁.wr]; exact hs.wr, by
      rw [a₁.base, ha]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  refine wp_stx (s := { s₁ with xmm := f }) hwr (WP.block_nil ?_)
  refine ⟨a₁.of_gpr rfl rfl rfl rfl, bm, g₁, z₁, ?_, ev, fun q hq => ?_, fun k' hk' q hq => ?_⟩
  · show Frame _ s.mem (s₁.mem.writeW (addr (s₁.gpr Impl.Modes.X86.sb) (32 + 16 * j)) (f e))
    rw [m₁, a₁.base, ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
  · show (s₁.mem.writeW (addr (s₁.gpr Impl.Modes.X86.sb) (32 + 16 * j)) (f e))
      (B.setWidth 64 + BitVec.ofNat 64 (32 + 16 * j + q)) = _
    rw [a₁.base, ← Offset.add_ofNat_add_ofNat, ← ha,
      ← byte_readW (s₁.mem.writeW (addr B (32 + 16 * j)) (f e)) (addr B (32 + 16 * j)) (w := 128) (k := q)
        (by omega_using [hq]),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact ev q hq
  · refine (bc q hq).trans ?_
    rw [e0 q hq, ke q hq, e2 q hq, xn, hx3 q hq, sg, hk' q hq]
    exact next_in _ _ _ _ _ _

end

/-! ## The block -/

/-- The two look-ups of a byte map are the map. -/
theorem cterms_sum (env : Nat → BitVec 8) (t v : Nat) : sum env (cterms t v) = nm t (mask env v nvars) := by
  simp only [cterms, sum, BitVec.xor_zero]; rfl

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

/-- The block in `xmm0` to its four words in the rounds' form, in the ring;
the last word left in `xmm1`, the exclusive-or of the last three in `xmm0`;
and the mask. -/
theorem head_wp (htb : s.gpr tbr = s.syms tableName) (hB : s.gpr Impl.Modes.X86.sb = B)
    (hwr : (⟨B.setWidth 64, 4 * 166⟩ : Region) ∈ s.wr) (hf : B.toNat + 664 ≤ 2 ^ 32) :
    WP isa (.block headX) s fun s' =>
      s'.gpr = s.gpr ∧ s'.zf = s.zf ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame ([80, 64, 48, 32].map fun lo => (⟨B.setWidth 64 + BitVec.ofNat 64 lo, 16⟩ : Region)) s.mem s'.mem ∧
      (∀ w < 4, ∀ q < 16, sAt s'.mem B (32 + 16 * w + q) = pl (byte (s.xmm .xmm0) (4 * w + q % 4))) ∧
      (∀ q < 16, byte (s'.xmm .xmm0) q = pl (byte (s.xmm .xmm0) (4 + q % 4)) ^^^
        pl (byte (s.xmm .xmm0) (8 + q % 4)) ^^^ pl (byte (s.xmm .xmm0) (12 + q % 4))) ∧
      (∀ q < 16, byte (s'.xmm .xmm1) q = pl (byte (s.xmm .xmm0) (12 + q % 4))) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have kn := (s.gpr kr).isLt
  have rel : Rel hparams (envOf hparams s) Regs.init s :=
    rel_init (p := hparams) htb (by show (s.gpr kr).toNat + 0 ≤ _; omega_using [kn])
      (fun o ho => absurd (show o + 16 ≤ 0 from ho) (by omega_arith))
  have ok : OutOk hparams hoparams s := by
    refine ⟨by show (s.gpr Impl.Modes.X86.sb).toNat + 96 ≤ _; rw [hB]; omega_using [hf],
      fun o ho => ⟨_, hwr, ?_⟩, ?_, by show (s.gpr kr).toNat + 0 ≤ _; omega_using [kn]⟩
    · show Region.Contains _ (addr (s.gpr Impl.Modes.X86.sb) o) 16
      have ho' : o + 16 ≤ 96 := ho
      rw [hB, addr_eq (by omega_using [hf, ho'])]
      exact Offset.contains_base _ (by omega_using [ho']) (by omega_using [ho'])
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
  have st : ∀ {o w : Nat}, outOk σ.2 o (hw w) = true → w < 4 → o = 32 + 16 * w → ∀ q < 16,
      sAt s'.mem B (32 + 16 * w + q) = pl (byte (s.xmm .xmm0) (4 * w + q % 4)) := fun {o w} ho hw4 he q hq => by
    have := hr.out ho hq
    rw [show (s.gpr hoparams.oreg) = s.gpr Impl.Modes.X86.sb from rfl, hB, ev' w hw4 q hq] at this
    rw [sAt, ← this, he]
  refine ⟨hr.gpr, hr.zf, hr.rd, hr.wr, hr.syms, ?_, fun w hw4 q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · have hfr := hr.frame
    rw [show (σ.2.map fun e => (⟨(s.gpr hoparams.oreg).setWidth 64 + BitVec.ofNat 64 e.1, 16⟩ : Region)) =
        ([80, 64, 48, 32].map fun lo => (⟨B.setWidth 64 + BitVec.ofNat 64 lo, 16⟩ : Region)) by
      rw [← ol, List.map_map]
      refine List.map_congr_left fun e _ => ?_
      exact congrArg (fun a : BitVec 32 => (⟨a.setWidth 64 + BitVec.ofNat 64 e.1, 16⟩ : Region)) hB] at hfr
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

theorem wk_sum (a b c k : Word) (q : Nat) : wl a q ^^^ wl b q ^^^ wl c q ^^^ wk k q = wk (a ^^^ b ^^^ c ^^^ k) q := by
  rw [wk_eq, wk_eq, wl_xor, wl_xor, wl_xor]
  xor_norm

/-- The block at byte 8 of the scratch buffer to the ring, the registers of
the loop, and the first round's input. -/
theorem cryptHead_wp (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 166)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (rk i)) :
    WP isa (.block (cryptHead ++ cryptKey)) s fun s' =>
      At s B 0 s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧ s'.gpr .eax = BitVec.ofNat 32 8 ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (rk i)) ∧
      (∀ w < 4, WordAt s'.mem B w (bwd s.mem B w)) ∧ Hw (s'.xmm .xmm1) (bwd s.mem B 3) ∧
      Hk (s'.xmm .xmm0) (bwd s.mem B 1 ^^^ bwd s.mem B 2 ^^^ bwd s.mem B 3 ^^^ rk 0) := by
  have hf : B.toNat + 664 ≤ 2 ^ 32 := hs.fit
  have hw : InRegions (s.rd ++ s.wr) (addr B 0) 4 := ⟨_, List.mem_append_right _ hs.wr, by
    rw [addr_eq (by omega_using [hf])]; exact Offset.contains_base _ (by decide) (by decide)⟩
  show WP isa (.block (.mov tbr (.mem ⟨Impl.Modes.X86.sb, 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) ::
    .alu .add kr (.imm 96) :: .mov .eax (.imm 8) ::
    .movdquLoad .xmm0 ⟨Impl.Modes.X86.sb, 8⟩ :: (headX ++ cryptKey))) s _
  refine Wp.wp_ldm hB hw fun s₁ u₁ => ?_
  refine Wp.wp_mov fun s₂ u₂ => ?_
  refine Wp.wp_addi fun s₃ u₃ => ?_
  refine Wp.wp_movi fun s₄ u₄ => ?_
  have e₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have y₄ : s₄.syms = s.syms := by rw [u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  have b₄ : s₄.gpr Impl.Modes.X86.sb = B := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have a₄ : At s B 0 s₄ := by
    refine ⟨b₄, ?_, r₄, w₄, y₄, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
        addr_eq (by omega_using [hf]), BitVec.add_zero]
      exact htab
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hB]
      rfl
  have c₄ : s₄.gpr .eax = BitVec.ofNat 32 8 := by rw [u₄.gpr]; rfl
  have ha8 : addr B 8 = B.setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega_using [hf])
  have hl : InRegions (s₄.rd ++ s₄.wr) (addr (s₄.gpr Impl.Modes.X86.sb) 8) 16 :=
    ⟨_, List.mem_append_right _ (by rw [w₄]; exact hs.wr), by
      rw [b₄, ha8]; exact Offset.contains_base _ (by decide) (by decide)⟩
  refine wp_ldx hl ?_
  obtain ⟨s₅, hs₅⟩ : ∃ s₅, s₅ = s₄.setXmm .xmm0 (s₄.mem.readW (addr (s₄.gpr Impl.Modes.X86.sb) 8) 128) := ⟨_, rfl⟩
  rw [← hs₅]
  have a₅ : At s B 0 s₅ := by subst hs₅; exact a₄.of_gpr rfl rfl rfl rfl
  have e₅ : s₅.mem = s.mem := by subst hs₅; exact e₄
  have c₅ : s₅.gpr .eax = BitVec.ofNat 32 8 := by subst hs₅; exact c₄
  have hbyte : ∀ k < 16, byte (s₅.xmm .xmm0) k = s.mem (B.setWidth 64 + BitVec.ofNat 64 (8 + k)) := fun k hk => by
    subst hs₅
    rw [RegUpd.xmm_setXmm_self]
    show (s₄.mem.readW (addr (s₄.gpr Impl.Modes.X86.sb) 8) 128).extractLsb' (8 * k) 8 = _
    rw [byte_readW _ _ (by omega_using [hk]), b₄, ha8, Offset.add_ofNat_add_ofNat, e₄]
  refine WP.block_append_iff.mpr (WP.mono (head_wp (B := B) (by rw [a₅.tb, a₅.syms]) a₅.base
    (by rw [a₅.wr]; exact hs.wr) hf) fun s₈ ⟨g₈, _, rd₈, wr₈, sy₈, f₈, wd₈, x0₈, x1₈, m₈⟩ => ?_)
  have a₈ : At s B 0 s₈ := a₅.of_gpr g₈ rd₈ wr₈ sy₈
  have pb : ∀ w < 4, ∀ q < 16, pl (byte (s₅.xmm .xmm0) (4 * w + q % 4)) = wl (bwd s.mem B w) q :=
    fun w hw4 q hq => by
    rw [hbyte _ (by omega_using [hw4]), wl, byteAt_bwd _ _ hw4 (Nat.mod_lt _ (by decide))]
  have f₈' : Frame ([80, 64, 48, 32].map fun lo => (⟨B.setWidth 64 + BitVec.ofNat 64 lo, 16⟩ : Region))
      s.mem s₈.mem := by
    have f' : Frame _ s₅.mem s₈.mem := f₈
    rwa [e₅] at f'
  have key₈ : ∀ i < 32, KeyAt s₈.mem B i (rk i) := fun i hi q hq => by
    rw [frame_sAt_list f₈' (fun lo hlo => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlo
      omega_using [hlo, hq]) (by omega_using [hi, hq]) (fun lo hlo => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlo
      omega_using [hlo])]
    exact hk i hi q hq
  have hkn := a₈.krNat hf (by decide)
  have hl₈ : InRegions (s₈.rd ++ s₈.wr) (addr (s₈.gpr kr) 0) 16 :=
    ⟨_, List.mem_append_right _ (by rw [a₈.wr]; exact hs.wr), by
      rw [addr_eq (by omega_using [hkn, hf]), a₈.kr64 hf (by decide), Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by decide) (by decide)⟩
  refine wp_ldx hl₈ (Wp.cons rfl (WP.block_nil ?_))
  refine ⟨a₈.of_gpr rfl rfl rfl rfl, fun q hq => m₈ q hq, ?_, ?_, key₈, fun w hw4 q hq => ?_, fun q hq => ?_,
    fun q hq => ?_⟩
  · show s₈.gpr .eax = _
    rw [g₈]; exact c₅
  · show Frame _ s.mem s₈.mem
    refine f₈'.sub fun r hr => ?_
    obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlo
    exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega_using [hlo]) (by omega_using [hlo])⟩
  · show sAt s₈.mem B (32 + 16 * w + q) = _
    rw [wd₈ w hw4 q hq, pb w hw4 q hq]
  · show byte (s₈.xmm .xmm1) q = _
    rw [x1₈ q hq]
    exact pb 3 (by decide) q hq
  · show byte (s₈.xmm .xmm0 ^^^ s₈.mem.readW (addr (s₈.gpr kr) 0) 128) q = _
    have kq : byte (s₈.mem.readW (addr (s₈.gpr kr) 0) 128) q = wk (rk 0) q := by
      show (s₈.mem.readW (addr (s₈.gpr kr) 0) 128).extractLsb' (8 * q) 8 = _
      rw [byte_readW _ _ (by omega_using [hq]), addr_eq (by omega_using [hkn, hf]), BitVec.add_zero,
        a₈.kr64 hf (by decide), Offset.add_ofNat_add_ofNat]
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

/-- The state with `n` turns left: the keys' pointer after `8 - n` turns,
the turns left in `eax`, the round keys, and the four words of the
specification's state after `4 (8 - n)` rounds in the ring, the last also
in `xmm1`, with `aesenclast`'s input for the next round in `xmm0`. -/
def Inv (s₀ : State) (B : BitVec 32) (rk : Nat → Word) (b : Spec.Sm4.Block) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ At s₀ B (8 - n) s ∧ (∀ q < 16, byte (s.xmm m0) q = 0x0f#8) ∧ s.gpr .eax = BitVec.ofNat 32 n ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s₀.mem s.mem ∧ (∀ i < 32, KeyAt s.mem B i (rk i)) ∧
    ∃ x0 x1 x2 x3, st rk b (4 * (8 - n)) = (x0, x1, x2, x3) ∧
      WordAt s.mem B 0 x0 ∧ WordAt s.mem B 1 x1 ∧ WordAt s.mem B 2 x2 ∧ WordAt s.mem B 3 x3 ∧
      Hw (s.xmm .xmm1) x3 ∧ (1 ≤ n → Hk (s.xmm .xmm0) (x1 ^^^ x2 ^^^ x3 ^^^ rk (4 * (8 - n))))

/-- A turn of the loop: four rounds. -/
theorem turn_wp (hs : ScrIn s₀ B 166) {b : Spec.Sm4.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
    WP isa (.block turn) s fun s' => s'.zf = some (decide (n = 1)) ∧ Inv s₀ B rk b (n - 1) s' := by
  obtain ⟨hn8, a, hm, hc, hfr, hk, x0, x1, x2, x3, hst, w0, w1, w2, w3, hx3, hin⟩ := hI
  have hin := hin hn
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a hst hin
  have hm8 : m < 8 := by omega_using [hn, hm']
  show WP isa (.block (round .xmm0 .xmm4 .xmm1 .xmm2 0 ++ (round .xmm4 .xmm0 .xmm2 .xmm1 1 ++
    (round .xmm0 .xmm4 .xmm1 .xmm2 2 ++ (round .xmm4 .xmm0 .xmm2 .xmm1 3 ++ Impl.Sm4.X86.AesNi.step))))) s _
  -- round `4 m`
  refine WP.block_append_iff.mpr (WP.mono (round_ok (j := 0) (a := .xmm0) (c := .xmm4) (nr := .xmm1) (e := .xmm2)
    (round_all 0 (by decide)) (by decide) (by decide)
    (by decide) (by decide) hs hm8 a hm hin hx3 w0 w2) fun s₁ ⟨a₁, m₁, g₁, z₁, f₁, e₁, wn₁, c₁⟩ => ?_)
  obtain ⟨x4, hx4⟩ : ∃ x4, x4 = x0 ^^^ Spec.Sm4.t (x1 ^^^ x2 ^^^ x3 ^^^ rk (4 * m)) := ⟨_, rfl⟩
  rw [← hx4] at e₁ wn₁ c₁
  have k₁ : ∀ i < 32, KeyAt s₁.mem B i (rk i) := fun i hi => (hk i hi).frame f₁ (by omega_using [hi]) (by decide)
  have w1₁ : WordAt s₁.mem B 1 x1 := w1.frame f₁ (by decide) (by decide) (by decide)
  have w2₁ : WordAt s₁.mem B 2 x2 := w2.frame f₁ (by decide) (by decide) (by decide)
  have w3₁ : WordAt s₁.mem B 3 x3 := w3.frame f₁ (by decide) (by decide) (by decide)
  have in₁ := c₁ _ (hk (4 * m + 0 + 1) (by omega_using [hm8]))
  -- round `4 m + 1`
  refine WP.block_append_iff.mpr (WP.mono (round_ok (j := 1) (a := .xmm4) (c := .xmm0) (nr := .xmm2) (e := .xmm1)
    (round_all 1 (by decide)) (by decide) (by decide)
    (by decide) (by decide) hs hm8 a₁ m₁ in₁ e₁ w1₁ w3₁) fun s₂ ⟨a₂, m₂, g₂, z₂, f₂, e₂, wn₂, c₂⟩ => ?_)
  obtain ⟨x5, hx5⟩ : ∃ x5, x5 = x1 ^^^ Spec.Sm4.t (x2 ^^^ x3 ^^^ x4 ^^^ rk (4 * m + 0 + 1)) := ⟨_, rfl⟩
  rw [← hx5] at e₂ wn₂ c₂
  have k₂ : ∀ i < 32, KeyAt s₂.mem B i (rk i) := fun i hi => (k₁ i hi).frame f₂ (by omega_using [hi]) (by decide)
  have w0₂ : WordAt s₂.mem B 0 x4 := wn₁.frame f₂ (by decide) (by decide) (by decide)
  have w2₂ : WordAt s₂.mem B 2 x2 := w2₁.frame f₂ (by decide) (by decide) (by decide)
  have w3₂ : WordAt s₂.mem B 3 x3 := w3₁.frame f₂ (by decide) (by decide) (by decide)
  have in₂ := c₂ _ (k₁ (4 * m + 1 + 1) (by omega_using [hm8]))
  -- round `4 m + 2`
  refine WP.block_append_iff.mpr (WP.mono (round_ok (j := 2) (a := .xmm0) (c := .xmm4) (nr := .xmm1) (e := .xmm2)
    (round_all 2 (by decide)) (by decide) (by decide)
    (by decide) (by decide) hs hm8 a₂ m₂ in₂ e₂ w2₂ w0₂) fun s₃ ⟨a₃, m₃, g₃, z₃, f₃, e₃, wn₃, c₃⟩ => ?_)
  obtain ⟨x6, hx6⟩ : ∃ x6, x6 = x2 ^^^ Spec.Sm4.t (x3 ^^^ x4 ^^^ x5 ^^^ rk (4 * m + 1 + 1)) := ⟨_, rfl⟩
  rw [← hx6] at e₃ wn₃ c₃
  have k₃ : ∀ i < 32, KeyAt s₃.mem B i (rk i) := fun i hi => (k₂ i hi).frame f₃ (by omega_using [hi]) (by decide)
  have w0₃ : WordAt s₃.mem B 0 x4 := w0₂.frame f₃ (by decide) (by decide) (by decide)
  have w1₃ : WordAt s₃.mem B 1 x5 := wn₂.frame f₃ (by decide) (by decide) (by decide)
  have w3₃ : WordAt s₃.mem B 3 x3 := w3₂.frame f₃ (by decide) (by decide) (by decide)
  have in₃ := c₃ _ (k₂ (4 * m + 2 + 1) (by omega_using [hm8]))
  -- round `4 m + 3`
  refine WP.block_append_iff.mpr (WP.mono (round_ok (j := 3) (a := .xmm4) (c := .xmm0) (nr := .xmm2) (e := .xmm1)
    (round_all 3 (by decide)) (by decide) (by decide)
    (by decide) (by decide) hs hm8 a₃ m₃ in₃ e₃ w3₃ w1₃) fun s₄ ⟨a₄, m₄, g₄, z₄, f₄, e₄, wn₄, c₄⟩ => ?_)
  obtain ⟨x7, hx7⟩ : ∃ x7, x7 = x3 ^^^ Spec.Sm4.t (x4 ^^^ x5 ^^^ x6 ^^^ rk (4 * m + 2 + 1)) := ⟨_, rfl⟩
  rw [← hx7] at e₄ wn₄ c₄
  have k₄ : ∀ i < 32, KeyAt s₄.mem B i (rk i) := fun i hi => (k₃ i hi).frame f₄ (by omega_using [hi]) (by decide)
  have w0₄ : WordAt s₄.mem B 0 x4 := w0₃.frame f₄ (by decide) (by decide) (by decide)
  have w1₄ : WordAt s₄.mem B 1 x5 := w1₃.frame f₄ (by decide) (by decide) (by decide)
  have w2₄ : WordAt s₄.mem B 2 x6 := wn₃.frame f₄ (by decide) (by decide) (by decide)
  have c₀ : s₄.gpr .eax = BitVec.ofNat 32 n := by rw [g₄, g₃, g₂, g₁, hc]
  show WP isa (.block [.alu .add kr (.imm 64), .alu .sub .eax (.imm 1)]) s₄ _
  refine wp_addi_x fun s₅ u₅ x₅ => wp_subi_x fun s₆ u₆ x₆ z₆ => WP.block_nil ?_
  have e₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have xe : s₆.xmm = s₄.xmm := by rw [x₆, x₅]
  have c₅ : s₅.gpr .eax = BitVec.ofNat 32 n := by rw [u₅.other _ (by decide), c₀]
  refine ⟨?_, by omega_using [hn8], ?_, by rw [xe]; exact m₄, ?_, ?_, by rw [e₆]; exact k₄, x4, x5, x6, x7, ?_,
    by rw [e₆]; exact w0₄, by rw [e₆]; exact w1₄, by rw [e₆]; exact w2₄, by rw [e₆]; exact wn₄,
    by rw [xe]; exact e₄, fun h1 => ?_⟩
  · rw [z₆, c₅, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [show 8 - (n - 1) = m + 1 by omega_using [hn, hm', hn8]]
    refine ⟨?_, ?_, by rw [u₆.rd, u₅.rd]; exact a₄.rd, by rw [u₆.wr, u₅.wr]; exact a₄.wr,
      by rw [u₆.syms, u₅.syms]; exact a₄.syms, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₄.base
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₄.esp
    · rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact a₄.tb
    · rw [u₆.other _ (by decide), u₅.gpr, a₄.kp, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
        Offset.add_ofNat_add_ofNat]
      congr 2
  · rw [u₆.gpr, c₅]; exact Wp.ofNat_pred hn
  · rw [e₆]
    exact (((hfr.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact ring_sub B (by decide)⟩)).trans
      (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact ring_sub B (by decide)⟩)).trans
      (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact ring_sub B (by decide)⟩)).trans
      (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact ring_sub B (by decide)⟩)
  · rw [show 4 * (8 - (n - 1)) = 4 * m + 1 + 1 + 1 + 1 by omega_using [hn, hm', hn8], st_succ, st_succ, st_succ,
      st_succ, hst, hx7, hx6, hx5, hx4]
    rfl
  · rw [xe, show 4 * (8 - (n - 1)) = 4 * m + 3 + 1 by omega_using [hn, hm', hn8]]
    exact c₄ _ (k₃ (4 * m + 3 + 1) (by omega_using [h1, hn, hm', hn8]))

/-- The eight turns: the four words after the 32 rounds, in the ring. -/
theorem loop_wp (hs : ScrIn s₀ B 166) {b : Spec.Sm4.Block} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ B rk b n s) :
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
theorem cryptTail_wp {n : Nat} (hs : ScrIn s₀ B 166) (h : At s₀ B n s) (hm : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8)
    {x : Nat → Word} (hw : ∀ w < 4, WordAt s.mem B w (x w)) :
    WP isa (.block cryptTail) s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s₀.gpr .esp ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.syms = s₀.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 8, 16⟩] s.mem s'.mem ∧
      ∀ q < 16, s'.mem (B.setWidth 64 + BitVec.ofNat 64 8 + BitVec.ofNat 64 q) = byteAt (x (3 - q / 4)) (q % 4) := by
  have hf : B.toNat + 664 ≤ 2 ^ 32 := hs.fit
  have he := h.env hs hm
  have hok := conv_all.2
  unfold tailOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨h2, c2⟩ := hok
  refine WP.block_append_iff.mpr (run_wp he.rel hrun fun s₁ hr hsame => ?_)
  have v : ∀ q < 16, byte (s₁.xmm .xmm2) q = byteAt (x (3 - q / 4)) (q % 4) := fun q hq => by
    have hlt : oR + 16 * (3 - q / 4) + q % 4 < 96 := by show 32 + 16 * (3 - q / 4) + q % 4 < 96; omega_arith
    have e : kb s (oR + 16 * (3 - q / 4) + q % 4) = wl (x (3 - q / 4)) (q % 4) := by
      rw [h.scr]; exact hw _ (by omega_arith) _ (by omega_arith)
    rw [hr.bytes h2 q hq, BV.same_eval _ (List.all_eq_true.mp c2 q (List.mem_range.mpr hq)), BV.eval, mask_zero,
      cterms_sum, BitVec.zero_xor, BitVec.xor_zero, env_key hlt, e, wl, Nat.mod_mod]
    exact pv_pl _
  obtain ⟨f, rfl⟩ := hsame
  have ha : addr B 8 = B.setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega_using [hf])
  have hwr : InRegions s.wr (addr (s.gpr Impl.Modes.X86.sb) 8) 16 := ⟨_, by rw [h.wr]; exact hs.wr, by
    rw [h.base, ha]; exact Offset.contains_base _ (by decide) (by decide)⟩
  refine wp_stx (s := { s with xmm := f }) hwr (WP.block_nil ?_)
  refine ⟨h.base, h.esp, h.rd, h.wr, h.syms, ?_, fun q hq => ?_⟩
  · show Frame _ s.mem (s.mem.writeW (addr (s.gpr Impl.Modes.X86.sb) 8) (f .xmm2))
    rw [h.base, ha]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
  · show (s.mem.writeW (addr (s.gpr Impl.Modes.X86.sb) 8) (f .xmm2)) _ = _
    rw [h.base, ← ha,
      ← byte_readW (s.mem.writeW (addr B 8) (f .xmm2)) (addr B 8) (w := 128) (k := q) (by omega_using [hq]),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact v q hq

/-- `crypt` enciphers the block at byte 8 of the scratch buffer, under the
round keys in their places, and changes nothing else but the ring. -/
theorem crypt_wp {k : Spec.Sm4.Schedule} (hB : s.gpr Impl.Modes.X86.sb = B) (hs : ScrIn s B 166)
    (htab : s.mem.readW (B.setWidth 64) 32 = s.syms tableName) (hk : ∀ i < 32, KeyAt s.mem B i (k.getD i 0)) :
    WP isa crypt s fun s' => s'.gpr Impl.Modes.X86.sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 8, 16⟩, ⟨B.setWidth 64 + BitVec.ofNat 64 32, 64⟩] s.mem s'.mem ∧
      (∀ i < 32, KeyAt s'.mem B i (k.getD i 0)) ∧
      Spec.Aes.bytesAt s'.mem (B.setWidth 64 + BitVec.ofNat 64 8) 16 =
        Spec.Sm4.cipher k (Spec.Aes.bytesAt s.mem (B.setWidth 64 + BitVec.ofNat 64 8) 16) := by
  obtain ⟨rk, hrk⟩ : ∃ rk : Nat → Word, rk = fun i => k.getD i 0 := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk, blk = Spec.Sm4.blockAt s.mem (B.setWidth 64 + BitVec.ofNat 64 8) := ⟨_, rfl⟩
  have hk' : ∀ i < 32, KeyAt s.mem B i (rk i) := by rw [hrk]; exact hk
  show WP isa (.seq (.block (cryptHead ++ cryptKey)) (.seq (.loop (.block turn) .ne) (.block cryptTail))) s _
  refine WP.seq (WP.mono (cryptHead_wp hB hs htab hk') fun s₁ ⟨a₁, m₁, c₁, f₁, k₁, w₁, x₁, y₁⟩ => ?_)
  have hI : Inv s B rk blk 8 s₁ := by
    refine ⟨Nat.le_refl _, a₁, m₁, c₁, f₁, k₁, bwd s.mem B 0, bwd s.mem B 1, bwd s.mem B 2, bwd s.mem B 3, ?_,
      w₁ 0 (by decide), w₁ 1 (by decide), w₁ 2 (by decide), w₁ 3 (by decide), x₁, fun _ => y₁⟩
    rw [hblk]; rfl
  refine WP.seq (WP.mono (loop_wp hs (by decide) hI) fun s₂ ⟨_, a₂, m₂, _, f₂, k₂, x0, x1, x2, x3, h32, v0, v1, v2, v3, _, _⟩ => ?_)
  have hw : ∀ w < 4, WordAt s₂.mem B w ([x0, x1, x2, x3].getD w 0) := fun w hw4 => by
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw4]) with rfl | rfl | rfl | rfl
    · exact v0
    · exact v1
    · exact v2
    · exact v3
  refine WP.mono (cryptTail_wp hs a₂ m₂ hw) fun s₃ ⟨b₃, e₃, r₃, w₃, y₃, f₃, v₃⟩ => ⟨b₃, e₃, r₃, w₃, y₃, ?_, ?_, ?_⟩
  · exact (f₂.mono fun r hr => List.mem_cons_of_mem _ hr).trans (f₃.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)
  · intro i hi q hq
    have := f₃.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * i + q), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_using [hi, hq]) (by decide))
      (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    have e := k₂ i hi q hq
    rw [hrk] at e
    rw [sAt, this]
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
  scr : ScrIn s₀ B 166
  sch : (⟨p.setWidth 64, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr
  pfit : p.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨p.setWidth 64, 128⟩ ⟨B.setWidth 64, 664⟩

/-- A state of `prepare` after `i` groups of four round keys: the
schedule's pointer, the round keys' pointer, the table's address, and the
mask. -/
structure PAt (s₀ : State) (B p : BitVec 32) (i : Nat) (s : State) : Prop where
  base : s.gpr Impl.Modes.X86.sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  sp : s.gpr .eax = p + BitVec.ofNat 32 (16 * i)
  kp : s.gpr kr = B + BitVec.ofNat 32 (96 + 64 * i)
  msk : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8

variable {s₀ s : State} {B p : BitVec 32} {i : Nat} {M : Mem}

theorem PAt.kr64 (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 (96 + 64 * i) := by
  have hf := he.scr.fit
  rw [h.kp]; exact addr_eq (by omega_arith)

theorem PAt.krNat (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr kr).toNat = B.toNat + (96 + 64 * i) := by
  have hf := he.scr.fit
  rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 96 + 64 * i) (by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem PAt.ax64 (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
  have hf := he.pfit
  rw [h.sp]; exact addr_eq (by omega_arith)

theorem PAt.axNat (h : PAt s₀ B p i s) (he : PEnv s₀ B p) (hi : i < 8) :
    (s.gpr .eax).toNat = p.toNat + 16 * i := by
  have hf := he.pfit
  rw [h.sp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- Four round keys of the schedule to their places (`prepGroupX`). -/
theorem prepGroupX_wp (he : PEnv s₀ B p) (hi : i < 8) (h : PAt s₀ B p i s) (hS : Sch M s.mem p) :
    WP isa (.block prepGroupX) s fun s' => PAt s₀ B p i s' ∧ s'.gpr .ecx = s.gpr .ecx ∧
      Frame [⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 64 * i), 64⟩] s.mem s'.mem ∧
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
    refine ⟨by show (s.gpr kr).toNat + 64 ≤ _; omega_arith, fun o ho => ⟨_, by rw [h.wr]; exact he.scr.wr, ?_⟩, ?_,
      by show (s.gpr .eax).toNat + 16 ≤ _; omega_arith⟩
    · show Region.Contains _ (addr (s.gpr kr) o) 16
      have ho' : o + 16 ≤ 64 := ho
      rw [addr_eq (by omega_arith), h.kr64 he hi, Offset.add_ofNat_add_ofNat]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · show Region.Disjoint ⟨(s.gpr .eax).setWidth 64, 16⟩ ⟨(s.gpr kr).setWidth 64, 64⟩
      rw [h.ax64 he hi, h.kr64 he hi]
      exact (he.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  have hok := prep_all.1
  unfold prepGroupOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, oin⟩, cm⟩ := hok
  refine runS_wp ok (RelS.init rel rfl) hrun fun s' hr => ?_
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at cm
  have st : ∀ {w : Nat}, outOk σ.2 (16 * w) (pw w) = true → w < 4 → KeyAt s'.mem B (4 * i + w) (rkAt M p (4 * i + w)) :=
    fun {w} ho hw4 q hq => by
    have h4 : q % 4 < 4 := Nat.mod_lt _ (by decide)
    have := hr.out ho hq
    rw [show (s.gpr poparams.oreg) = s.gpr kr from rfl, h.kr64 he hi, Offset.add_ofNat_add_ofNat] at this
    rw [sAt, show 96 + 16 * (4 * i + w) + q = 96 + 64 * i + (16 * w + q) by omega_arith, this, pw, BV.eval, mask_zero,
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
    (hf : Frame [⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩] m m') (han : a + n ≤ 664) : Sch M m' p := fun o ho => by
  rw [← h o ho]
  refine hf.bytes (R := ⟨p.setWidth 64, 128⟩) (fun r hr => ?_) (by show (128 : Nat) ≤ 2 ^ 64; decide) ho
  rw [List.mem_singleton] at hr; subst hr
  exact he.sep.sub_right (Offset.sub_base _ han)

/-- The loop's invariant, with `n` groups left, from the memory `m₁`. -/
def PInv (s₀ : State) (M m₁ : Mem) (B p : BitVec 32) (n : Nat) (s : State) : Prop :=
  n ≤ 8 ∧ PAt s₀ B p (8 - n) s ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ Sch M s.mem p ∧
    Frame [⟨B.setWidth 64 + BitVec.ofNat 64 96, 512⟩] m₁ s.mem ∧
    ∀ j < 4 * (8 - n), KeyAt s.mem B j (rkAt M p j)

theorem pturn_wp {m₁ : Mem} (he : PEnv s₀ B p) {n : Nat} (hn : 1 ≤ n) (hI : PInv s₀ M m₁ B p n s) :
    WP isa (.block prepGroup) s fun s' => s'.zf = some (decide (n = 1)) ∧ PInv s₀ M m₁ B p (n - 1) s' := by
  obtain ⟨hn8, a, hc, hS, hF, K⟩ := hI
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  rw [← hm'] at a K
  have hm8 : m < 8 := by omega_using [hn, hm']
  have hf := he.scr.fit
  refine WP.block_append_iff.mpr (WP.mono (prepGroupX_wp he hm8 a hS) fun s₁ ⟨a₁, c₁, f₁, k₁⟩ => ?_)
  show WP isa (.block [.alu .add .eax (.imm 16), .alu .add kr (.imm 64), .alu .sub .ecx (.imm 1)]) s₁ _
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
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, Offset.add_ofNat_add_ofNat]
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
      have := f₁.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * j + q), 1⟩) (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_using [hj', hq])) (by omega_using [hj', hq, hm8])
          (by omega_using [hm8])) (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
      rw [BitVec.add_zero] at this
      rw [sAt, this]
      exact K j hj' q hq
    · have := k₁ (j - 4 * m) (by omega_using [hj, hj', hn, hm', hn8])
      rwa [show 4 * m + (j - 4 * m) = j by omega_using [hj']] at this

/-- The eight groups: the 32 round keys in their places. -/
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
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 664⟩) :
    WP isa (.block prepHead) s fun s' => PAt s B p 0 s' ∧ s'.gpr .ecx = BitVec.ofNat 32 8 ∧ Sch M s'.mem p ∧
      Frame [⟨B.setWidth 64, 4⟩] s.mem s'.mem ∧ s'.mem.readW (B.setWidth 64) 32 = s.syms tableName := by
  have hf := he.scr.fit
  have hpf := he.pfit
  have ha0 : addr B 0 = B.setWidth 64 := by rw [addr_eq (by omega_arith), BitVec.add_zero]
  have hw : InRegions s.wr (addr B 0) 4 := ⟨_, he.scr.wr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  show WP isa (.block (.store ⟨Impl.Modes.X86.sb, 0⟩ .eax :: .mov tbr (.reg .eax) ::
    .mov .eax (.mem ⟨.esp, 4 + 4 * 0⟩) :: .mov kr (.reg Impl.Modes.X86.sb) :: .alu .add kr (.imm 96) ::
    .mov .ecx (.imm 8) :: [tb m0 oM0])) s _
  refine Wp.wp_stm hB hw fun s₂ u₂ => ?_
  have f₂ : Frame [⟨B.setWidth 64, 4⟩] s.mem s₂.mem := by
    rw [u₂.mem, ha0]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)
  have sub4 : Region.Sub ⟨B.setWidth 64, 4⟩ ⟨B.setWidth 64, 664⟩ := Region.sub_prefix (by decide)
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
  have k₇ : s₇.gpr kr = B + BitVec.ofNat 32 (96 + 64 * 0) := by
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

/-- `prepare` leaves the round keys of the schedule in their places, and the
table's address in the scratch buffer's first slot; it writes only the
core's slots, and the four bytes below `esp` of the frame that gets the
table's address. -/
theorem prepare_wp (hB : s.gpr Impl.Modes.X86.sb = B) (he : PEnv s B p) (hesp : 4 ≤ (s.gpr .esp).toNat)
    (hin0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4) (hp : s.mem.readW (s.ea (argOp 0)) 32 = p)
    (h0B : Region.Disjoint ⟨s.ea (argOp 0), 4⟩ ⟨B.setWidth 64, 664⟩)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨p.setWidth 64, 128⟩)
    (h0S : Region.Disjoint (below (s.gpr .esp) 4) ⟨s.ea (argOp 0), 4⟩) :
    WP isa prepare s fun s' => (∀ i < 32, KeyAt s'.mem B i (rkAt s.mem p i)) ∧
      s'.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧ s'.gpr Impl.Modes.X86.sb = B ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨B.setWidth 64, 624⟩, below (s.gpr .esp) 4] s.mem s'.mem := by
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
their places, and the table's address in the first slot. -/
def Ready (s : State) (B : BitVec 32) (k : Spec.Sm4.Schedule) : Prop :=
  (∀ i < 32, KeyAt s.mem B i (k.getD i 0)) ∧ s.mem.readW (B.setWidth 64) 32 = s.syms tableName ∧
    B.toNat + 664 ≤ 2 ^ 32

theorem core_slots : core.slots = 156 := rfl

/-- The key stays ready through what a mode writes outside the core's slots
or within its buffer. -/
theorem ready_frame {s s' : State} {B : BitVec 32} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : Ready s B k) (hsy : s'.syms = s.syms) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion core B) r ∨ Region.Sub r (blkRegion core B)) : Ready s' B k := by
  obtain ⟨hk, ht, hfit⟩ := h
  have keep : ∀ {a n : Nat}, a + n ≤ 624 → (a + n ≤ 8 ∨ 24 ≤ a) → ∀ r ∈ rs,
      Region.Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 a, n⟩ r := fun {a n} h₁ h₂ r hr => by
    rcases hd r hr with h | h
    · exact h.sub_left (Offset.sub_base _ (by rw [core_slots]; omega_arith))
    · exact (Offset.disjoint (B.setWidth 64) (d := a) (n := n) (e := 4 * core.buf) (k := 4 * core.bw * core.G)
        (by show a + n ≤ 8 ∨ 8 + 16 ≤ a; omega_arith) (by omega_arith) (by decide)).sub_right h
  refine ⟨fun i hi q hq => ?_, ?_, hfit⟩
  · have := hf.bytes (R := ⟨B.setWidth 64 + BitVec.ofNat 64 (96 + 16 * i + q), 1⟩)
      (keep (by omega_arith) (.inr (by omega_arith))) (by show (1 : Nat) ≤ 2 ^ 64; decide) (i := 0)
      (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    rw [sAt, this]
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
