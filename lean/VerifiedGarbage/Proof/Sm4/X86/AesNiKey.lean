module

public import VerifiedGarbage.Proof.Sm4.X86.AesNiKeyMaps
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiKeyMaps
public import VerifiedGarbage.Proof.Sm4.X86.AesNiKeyLit
meta import VerifiedGarbage.Proof.Sm4.X86.AesNiKeyLit
public import VerifiedGarbage.Proof.Sm4.Rounds
meta import VerifiedGarbage.Proof.Sm4.Rounds
public import VerifiedGarbage.Spec.Sm4.Contract
meta import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
meta import VerifiedGarbage.Proof.Sm4.X86.KeyVerified
import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# The SM4 key schedule by the AES S-box on x86 (32-bit) meets its contract

`expandKey_wp`: `Impl.Sm4.X86.AesNiKey.expandKey` leaves at `schedule` the
round keys of `Spec.Sm4.expandKey`, as the rounds in place of
`Proof/Sm4/Rounds.lean` (`quads .key`), a turn of the loop four of them.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.AesNiKey

open VG VG.X86 VG.X86.ByteMap VG.Impl.Sm4.X86.AesNiKey
open VG.Proof.Sm4 (sboxB byteAt getLsbD_byteAt getLsbD_tau)
open VG.Spec.Sm4 (Word)
open VG.Impl.Sm4 (Lin)

/-! ## The byte maps -/

theorem byte_ofNat (b : Byte) : BitVec.ofNat 8 b.toNat = b := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `sbox_all`, of a byte. -/
theorem sbox_ok (b : Byte) {r : Nat} (hr : r < 4) : am (oQ + 32 * r) (aesSbox (pk b)) = pl (kn r (sboxB b)) := by
  have h := List.all_eq_true.mp sbox_all b.toNat (List.mem_range.mpr b.isLt)
  have h := List.all_eq_true.mp h r (List.mem_range.mpr hr)
  rw [byte_ofNat, beq_iff_eq] at h
  exact h

theorem pv_pl (b : Byte) : pv (pl b) = b := by
  have h := List.all_eq_true.mp inv_all b.toNat (List.mem_range.mpr b.isLt)
  rw [byte_ofNat, beq_iff_eq] at h
  exact h

/-- A nibble table of `pl`, of nibbles. -/
theorem lk_xor {t : Nat} (ht : t ∈ [oCV, oCV + 16]) {x y : Byte}
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

/-- The byte map into the rounds' form is linear. -/
theorem pl_xor (u v : Byte) : pl (u ^^^ v) = pl u ^^^ pl v := by
  have e₁ : (u ^^^ v) &&& 0x0f#8 = u &&& 0x0f#8 ^^^ v &&& 0x0f#8 := Fn.lin_xor (g := .and 0x0f#8) rfl u v
  have e₂ : (u ^^^ v) >>> 4 = u >>> 4 ^^^ v >>> 4 := Fn.lin_xor (g := .hi4) rfl u v
  unfold pl nm
  rw [e₁, e₂, lk_xor (by decide) (lo_lt u) (lo_lt v), lk_xor (by decide) (hi_lt u) (hi_lt v)]
  ac_rfl

/-- Exclusive-ors of bytes, up to order and pairs that cancel. -/
theorem xor_x3 (a b : Byte) : a ^^^ (a ^^^ b) = b := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
theorem xor_lc (a b c : Byte) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by ac_rfl
macro "xor_norm" : tactic =>
  `(tactic| simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_lc, xor_x3, BitVec.xor_self, BitVec.xor_zero,
    BitVec.zero_xor])

/-! ## The bytes of a word -/

theorem byteAt_xor (a b : Word) (k : Nat) : byteAt (a ^^^ b) k = byteAt a k ^^^ byteAt b k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [byteAt, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, hj, decide_true,
    Bool.true_and]

theorem byteAt_tau (x : Word) {k : Nat} (hk : k < 4) : byteAt (Spec.Sm4.tau x) k = sboxB (byteAt x k) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_byteAt _ hk hj, getLsbD_tau x hk hj]

/-- Words with the same four bytes are equal. -/
theorem word_ext {a b : Word} (h : ∀ k < 4, byteAt a k = byteAt b k) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun v : Byte => v.getLsbD (i % 8)) (h (3 - i / 8) (by omega_using [hi]))
  simp only [getLsbD_byteAt _ (show 3 - i / 8 < 4 by omega_using [hi]) (Nat.mod_lt i (by decide))] at e
  rwa [show 8 * (3 - (3 - i / 8)) + i % 8 = i by omega_using [hi]] at e

/-- `kn_all`, of a byte. -/
theorem kn_ok (x : Byte) {j : Nat} (hj : j < 8) :
    (kn 1 x).getLsbD j = (decide (5 ≤ j) && x.getLsbD (j - 5)) ∧
    (kn 2 x).getLsbD j = ((decide (j < 5) && x.getLsbD (j + 3)) ^^ (decide (j = 7) && x.getLsbD 0)) ∧
    (kn 3 x).getLsbD j = (decide (j < 7) && x.getLsbD (j + 1)) := by
  have h := List.all_eq_true.mp kn_all x.toNat (List.mem_range.mpr x.isLt)
  have h := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [byte_ofNat] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Bit `j` of the byte `k` of a word. -/
def wb (k j : Nat) : Nat := 8 * (3 - k) + j

/-- The bits of a word whose exclusive-or is bit `j` of
`b[k] ⊕ kn 1 b[k+1] ⊕ kn 2 b[k+2] ⊕ kn 3 b[k+3]`. -/
def kIdx (k j : Nat) : List Nat :=
  [wb k j] ++ (if 5 ≤ j then [wb ((k + 1) % 4) (j - 5)] else []) ++
  (if j < 5 then [wb ((k + 2) % 4) (j + 3)] else []) ++ (if j = 7 then [wb ((k + 2) % 4) 0] else []) ++
  (if j < 7 then [wb ((k + 3) % 4) (j + 1)] else [])

theorem kIdx_perm : ∀ k < 4, ∀ j < 8, (kIdx k j).Perm (Proof.Sm4.keyIdx (wb k j)) := by decide

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

/-- §7.3: a byte of `L'(B)`, of the byte there and the three after it. -/
theorem byteAt_keyLinear (B : Word) {k : Nat} (hk : k < 4) :
    byteAt (Spec.Sm4.keyLinear B) k =
      kn 0 (byteAt B k) ^^^ kn 1 (byteAt B ((k + 1) % 4)) ^^^ kn 2 (byteAt B ((k + 2) % 4)) ^^^
        kn 3 (byteAt B ((k + 3) % 4)) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have k1 : (k + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  have k2 : (k + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  have k3 : (k + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [getLsbD_byteAt _ hk hj]
  have hl := Proof.Sm4.getLsbD_fn .key B (k := 8 * (3 - k) + j) (by omega_using [hk, hj])
  rw [show Impl.Sm4.Lin.fn .key = Spec.Sm4.keyLinear from rfl] at hl
  rw [hl, show Impl.Sm4.Lin.idx .key (8 * (3 - k) + j) = Proof.Sm4.keyIdx (wb k j) from rfl,
    ← Proof.Sm4.idxXor_perm B (kIdx_perm k hk j hj)]
  simp only [BitVec.getLsbD_xor, (kn_ok _ hj).1, (kn_ok _ hj).2.1, (kn_ok _ hj).2.2, show ∀ b : Byte, kn 0 b = b from fun _ => rfl]
  rw [getLsbD_byteAt _ hk hj, cond_bit B (5 ≤ j) k1 (fun _ => by omega_using [hj]),
    cond_bit B (j < 5) k2 (fun h => by omega_using [h]), cond_bit B (j = 7) k2 (fun _ => by decide),
    cond_bit B (j < 7) k3 (fun h => by omega_using [h])]
  simp only [kIdx, idxXor_append, idxXor_ite, idxXor_one, wb, Bool.xor_assoc]

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

theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (Spec.Sm4.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Sm4.blockAt, Vector.getD, hi]

/-- The schedule's words are little-endian. -/
theorem byteAt_sched (m : Mem) (p : Addr) {i k : Nat} (hi : i < 32) (hk : k < 4) :
    byteAt ((Spec.Sm4.scheduleAt m p)[i]'hi) k = m (p + BitVec.ofNat 64 (4 * i + (3 - k))) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_byteAt _ hk hj, Proof.Sm4.getLsbD_scheduleAt m _ hi (by omega_using [hk]) hj]

/-! ## What the parts of the code compute -/

/-- Byte `o` of the turn's row at `edx`. -/
def kb (s : State) (o : Nat) : Byte := s.mem ((s.gpr kp).setWidth 64 + BitVec.ofNat 64 o)

/-- What a part of the loop needs of the state: the table's address in its
register, the turn's row readable at `edx`, and the mask. -/
structure Env (s : State) : Prop where
  tb : s.gpr tbr = s.syms tableName
  fit : (s.gpr kp).toNat + 16 ≤ 2 ^ 32
  acc : InRegions (s.rd ++ s.wr) (addr (s.gpr kp) 0) 16
  msk : ∀ i < 16, byte (s.xmm m0) i = 0x0f#8

/-- A register that holds the word `X` in the rounds' form, in its first lane. -/
def Hw0 (v : BitVec 128) (X : Word) : Prop := ∀ q < 4, byte v q = pl (byteAt X q)

/-- The four byte maps of `aesenclast`'s S-boxes, at byte `q` of the first
lane, of its input bytes `t`. -/
def ksum (t : Nat → Byte) (q : Nat) : Byte :=
  am (oQ + 32 * 0) (aesSbox (t (srow (4 * 0 + q)))) ^^^ am (oQ + 32 * 1) (aesSbox (t (srow (4 * 1 + q)))) ^^^
    am (oQ + 32 * 2) (aesSbox (t (srow (4 * 2 + q)))) ^^^ am (oQ + 32 * 3) (aesSbox (t (srow (4 * 3 + q))))

section
variable {s s' : State} {ρ : Regs}

theorem env_var (p : Params) (r : XReg) {q : Nat} (hq : q < 16) :
    mask (envOf p s) (var r q) nvars = byte (s.xmm r) q := by
  have hr : r.ctorIdx < 8 := by cases r <;> decide
  rw [var, mask_bit _ (by show 16 * r.ctorIdx + q < 1024; omega_using [hr, hq]), envOf_reg p s r hq]

theorem env_key (p : Params) {o : Nat} (ho : o < 16) :
    mask (envOf p s) (kv o) nvars = s.mem ((s.gpr p.kreg).setWidth 64 + BitVec.ofNat 64 o) := by
  rw [kv, mask_bit _ (by show 128 + o < 1024; omega_using [ho]), envOf_key]

theorem keeps_ok {p : Params} (hr : Rel p (envOf p s) ρ s') {r : XReg} (h : keeps ρ r = true) :
    ∀ q < 16, byte (s'.xmm r) q = byte (s.xmm r) q := fun q hq => by
  simp only [keeps, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [hr.bytes h.1 q hq, BV.same_eval _ (List.all_eq_true.mp h.2 q (List.mem_range.mpr hq))]
  simp only [BV.eval, sum, BitVec.xor_zero, env_var p r hq]

theorem mask_ok {p : Params} (hr : Rel p (envOf p s) ρ s') (h : maskOk ρ = true) :
    ∀ q < 16, byte (s'.xmm m0) q = 0x0f#8 := fun q hq => by
  simp only [maskOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [hr.bytes h.1 q hq, BV.same_eval _ (List.all_eq_true.mp h.2 q (List.mem_range.mpr hq)), BV.cst_eval]

/-- The two look-ups of a byte map are the map. -/
theorem cterms_sum (env : Nat → BitVec 8) (t v : Nat) : sum env (cterms t v) = nm t (mask env v nvars) := by
  simp only [cterms, sum, BitVec.xor_zero]; rfl

theorem aT_sum (env : Nat → BitVec 8) (t : Nat) (a : XReg) (p : Nat) :
    sum env (aT t a p) = am t (aesSbox (mask env (var a (srow p)) nvars)) := by
  simp only [aT, sum, BitVec.xor_zero]; rfl

theorem Env.relP (h : Env s) : Rel pparams (envOf pparams s) regs₀ s :=
  (rel_init (p := pparams) h.tb h.fit fun o ho => by
    have e : o = 0 := by have : o + 16 ≤ 16 := ho; omega_using [this]
    subst e; exact h.acc).const m0 h.msk

theorem Env.relR (h : Env s) : Rel rparams (envOf rparams s) regs₀ s :=
  (rel_init (p := rparams) h.tb (by show (s.gpr kp).toNat + 0 ≤ _; have := h.fit; omega_using [this])
    fun o ho => absurd (show o + 16 ≤ 0 from ho) (by omega_arith)).const m0 h.msk

theorem Env.same (h : Env s) (hs : Same s s') (hm : ∀ i < 16, byte (s'.xmm m0) i = 0x0f#8) : Env s' := by
  obtain ⟨f, rfl⟩ := hs
  exact ⟨h.tb, h.fit, h.acc, hm⟩

theorem xreg_mem {u : Nat} (hu : u < 4) : xreg u ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm3] := by
  rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega_using [hu]) with rfl | rfl | rfl | rfl <;> decide

theorem xreg_ne {u w : Nat} (hu : u < 4) (hw : w < 4) (h : u ≠ w) : xreg u ≠ xreg w := by
  rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega_using [hu]) with rfl | rfl | rfl | rfl <;>
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw]) with rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl h | decide

/-- The first half of round `w` of a turn: `aesenclast`'s input. -/
theorem prep_wp {v1 v2 v3 : XReg} {w : Nat} (hok : prepOk v1 v2 v3 w = true) (hw : w < 4) (he : Env s) :
    WP isa (.block (prepX v1 v2 v3 w)) s fun s' => Same s s' ∧
      (∀ i < 16, byte (s'.xmm .xmm4) i = kb s (4 * w + i / 4) ^^^ byte (s.xmm v1) (i / 4) ^^^
        byte (s.xmm v2) (i / 4) ^^^ byte (s.xmm v3) (i / 4)) ∧
      (∀ u < 4, ∀ q < 16, byte (s'.xmm (xreg u)) q = byte (s.xmm (xreg u)) q) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  unfold prepOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨h4, c4⟩, k0⟩, k1⟩, k2⟩, k3⟩, cm⟩ := hok
  refine run_wp he.relP hrun fun s' hr hsame => ⟨hsame, fun i hi => ?_, fun u hu => ?_, mask_ok hr cm⟩
  · have i4 : i / 4 < 16 := by omega_using [hi]
    rw [hr.bytes h4 i hi, BV.same_eval _ (List.all_eq_true.mp c4 i (List.mem_range.mpr hi))]
    simp only [BV.eval, mask_xor, sum, BitVec.xor_zero,
      env_key pparams (show 4 * w + i / 4 < 16 by omega_using [hw, hi]), env_var pparams v1 i4,
      env_var pparams v2 i4, env_var pparams v3 i4]
    rfl
  · rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega_using [hu]) with rfl | rfl | rfl | rfl
    · exact keeps_ok hr k0
    · exact keeps_ok hr k1
    · exact keeps_ok hr k2
    · exact keeps_ok hr k3

/-- The second half: the S-boxes and the four byte maps, added to `v0`. -/
theorem roundX_wp {v0 : XReg} (hok : roundOk v0 = true) (he : Env s) :
    WP isa (.block (roundX v0)) s fun s' => Same s s' ∧
      (∀ q < 4, byte (s'.xmm v0) q = byte (s.xmm v0) q ^^^ ksum (fun p => byte (s.xmm .xmm4) p) q) ∧
      (∀ u < 4, xreg u ≠ v0 → ∀ q < 16, byte (s'.xmm (xreg u)) q = byte (s.xmm (xreg u)) q) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  unfold roundOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨h0, c0⟩, ck⟩, cm⟩ := hok
  refine run_wp he.relR hrun fun s' hr hsame => ⟨hsame, fun q hq => ?_, fun u hu hne => ?_, mask_ok hr cm⟩
  · rw [hr.bytes h0 q (by omega_using [hq]), BV.same_eval _ (List.all_eq_true.mp c0 q (List.mem_range.mpr hq))]
    simp only [BV.eval, show List.range 4 = [0, 1, 2, 3] from rfl, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, sum_append, aT_sum, env_var rparams v0 (show q < 16 by omega_using [hq]),
      env_var rparams .xmm4 (srow_lt _), ksum, BitVec.xor_zero, BitVec.xor_assoc]
  · have h := List.all_eq_true.mp ck (xreg u) (xreg_mem hu)
    rw [Bool.or_eq_true, beq_iff_eq] at h
    exact keeps_ok hr (h.resolve_left hne)

/-- The turn's round keys in the schedule's format, in `xmm4`. -/
theorem out_wp (he : Env s) {y : Nat → Word} (hy : ∀ u < 4, Hw0 (s.xmm (xreg u)) (y u)) :
    WP isa (.block outX) s fun s' => Same s s' ∧
      (∀ q < 16, byte (s'.xmm .xmm4) q = byteAt (y (q / 4)) (3 - q % 4)) ∧
      (∀ u < 4, ∀ q < 16, byte (s'.xmm (xreg u)) q = byte (s.xmm (xreg u)) q) ∧
      (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) := by
  have hok := out_ok
  unfold outOk' at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨h4, c4⟩, k0⟩, k1⟩, k2⟩, k3⟩, cm⟩ := hok
  refine run_wp he.relR hrun fun s' hr hsame => ⟨hsame, fun q hq => ?_, fun u hu => ?_, mask_ok hr cm⟩
  · rw [hr.bytes h4 q hq, BV.same_eval _ (List.all_eq_true.mp c4 q (List.mem_range.mpr hq)), BV.eval, mask_zero,
      cterms_sum, BitVec.zero_xor, BitVec.xor_zero, env_var rparams _ (show 3 - q % 4 < 16 by omega_arith),
      hy _ (by omega_using [hq]) _ (by omega_arith)]
    exact pv_pl _
  · rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega_using [hu]) with rfl | rfl | rfl | rfl
    · exact keeps_ok hr k0
    · exact keeps_ok hr k1
    · exact keeps_ok hr k2
    · exact keeps_ok hr k3

theorem srow_div {r q : Nat} (hq : q < 4) : srow (4 * r + q) / 4 = (q + r) % 4 := by
  have e1 : (4 * r + q) % 4 = q := by omega_using [hq]
  have e2 : (4 * r + q) / 4 = r := by omega_using [hq]
  have e3 := Nat.mod_lt (r + q) (show 0 < 4 by decide)
  unfold srow
  rw [e1, e2, Nat.add_comm q r]
  omega_using [hq, e3]

/-- Round `w` of a turn, of the words: the round in place of
`Proof/Sm4/Rounds.lean`, with the constant `c` whose bytes the row has. -/
theorem round_ok {w : Nat} (hw : w < 4) (he : Env s) {x : Nat → Word} {c : Word}
    (hx : ∀ u < 4, Hw0 (s.xmm (xreg u)) (x u)) (hrow : ∀ j < 4, kb s (4 * w + j) = pk (byteAt c j)) :
    WP isa (.block (round (vr w) (vr (w + 1)) (vr (w + 2)) (vr (w + 3)) w)) s fun s' =>
      Same s s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      ∀ u < 4, Hw0 (s'.xmm (xreg u)) (Proof.Sm4.sround .key c w x u) := by
  obtain ⟨hp, hr⟩ := round_all w hw
  simp only [vr, Nat.mod_eq_of_lt hw] at hp hr
  show WP isa (.block (prepX (xreg ((w + 1) % 4)) (xreg ((w + 2) % 4)) (xreg ((w + 3) % 4)) w ++
    roundX (xreg (w % 4)))) s _
  rw [Nat.mod_eq_of_lt hw]
  refine WP.block_append_iff.mpr (WP.mono (prep_wp hp hw he) fun s₁ ⟨sm₁, t₁, k₁, m₁⟩ => ?_)
  refine WP.mono (roundX_wp hr (he.same sm₁ m₁)) fun s₂ ⟨sm₂, v₂, k₂, m₂⟩ => ?_
  refine ⟨sm₁.trans sm₂, m₂, fun u hu q hq => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = x ((w + 1) % 4) ^^^ x ((w + 2) % 4) ^^^ x ((w + 3) % 4) ^^^ c := ⟨_, rfl⟩
  have ht : ∀ i < 16, byte (s₁.xmm .xmm4) i = pk (byteAt Y (i / 4)) := fun i hi => by
    have h4 : i / 4 < 4 := by omega_using [hi]
    rw [t₁ i hi, hrow _ h4, hx _ (Nat.mod_lt _ (by decide)) _ h4, hx _ (Nat.mod_lt _ (by decide)) _ h4,
      hx _ (Nat.mod_lt _ (by decide)) _ h4, hY, pk, pk, byteAt_xor, byteAt_xor, byteAt_xor, pl_xor, pl_xor, pl_xor]
    xor_norm
  by_cases huw : u = w
  · subst huw
    have k1 : (q + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
    have k2 : (q + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
    have k3 : (q + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
    have ks : ksum (fun p => byte (s₁.xmm .xmm4) p) q = pl (byteAt (Spec.Sm4.keyT Y) q) := by
      rw [Spec.Sm4.keyT, byteAt_keyLinear _ hq, byteAt_tau _ hq, byteAt_tau _ k1, byteAt_tau _ k2, byteAt_tau _ k3,
        pl_xor, pl_xor, pl_xor, ← sbox_ok _ (r := 0) (by decide), ← sbox_ok _ (r := 1) (by decide),
        ← sbox_ok _ (r := 2) (by decide), ← sbox_ok _ (r := 3) (by decide)]
      simp only [ksum, ht _ (srow_lt _), srow_div (r := 0) hq, srow_div (r := 1) hq,
        srow_div (r := 2) hq, srow_div (r := 3) hq, Nat.add_zero, Nat.mod_eq_of_lt hq]
    rw [v₂ q hq, k₁ u hu q (by omega_using [hq]), hx u hu q hq, ks]
    unfold Proof.Sm4.sround
    rw [ite_eq_left rfl, VG.Impl.Sm4.Lin.t_key, ← hY, byteAt_xor, pl_xor]
  · rw [k₂ u hu (xreg_ne hu hw huw) q (by omega_using [hq]), k₁ u hu q (by omega_using [hq]), hx u hu q hq]
    unfold Proof.Sm4.sround
    rw [ite_eq_right huw]

end

/-! ## The constants, the key's words, and the loop -/

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

theorem wp_movi_x {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d v → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.setReg _ _ _) rfl)

/-- `movdqu [b + o], r`, to writable bytes. -/
theorem wp_stx {b : Reg} {o : Nat} {r : XReg} (hin : InRegions s.wr (addr (s.gpr b) o) 16)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.xmm r) } Q) :
    WP isa (.block (.movdquStore ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.xmm r) }) ?_ k
  show State.store128 s (addr (s.gpr b) o) _ = _
  rw [State.store128, ite_eq_left hin]

end

section
variable {s₀ s : State} {P K : BitVec 32}

/-- The table's row of `CK₄ₘ₊w`. -/
theorem ck_row {m w j : Nat} (hm : m < 8) (hw : w < 4) (hj : j < 4) :
    byte (tblAt (oCK + 16 * m)) (4 * w + j) = pk (byteAt (Spec.Sm4.ck (4 * m + w)) j) := by
  have h := List.all_eq_true.mp consts_all.2 (4 * m + w) (List.mem_range.mpr (by omega_using [hm, hw]))
  have h := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [beq_iff_eq, show (4 * m + w) / 4 = m by omega_using [hw], show (4 * m + w) % 4 = w by omega_using [hw]] at h
  exact h

/-- The eight rows of constants to the schedule's bytes (`stage`). -/
theorem stage_wp (htb : s.gpr tbr = s.syms tableName) (hP : s.gpr kp = P)
    (hwr : (⟨P.setWidth 64, 128⟩ : Region) ∈ s.wr) (hf : P.toNat + 128 ≤ 2 ^ 32) :
    WP isa (.block stage) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [⟨P.setWidth 64, 128⟩] s.mem s'.mem ∧
      ∀ m < 8, ∀ q < 16, s'.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * m + q)) = byte (tblAt (oCK + 16 * m)) q := by
  have cn := (s.gpr .ecx).isLt
  have rel : Rel sparams (envOf sparams s) Regs.init s :=
    rel_init (p := sparams) htb (by show (s.gpr .ecx).toNat + 0 ≤ _; omega_using [cn])
      (fun o ho => absurd (show o + 16 ≤ 0 from ho) (by omega_arith))
  have ok : OutOk sparams soparams s := by
    refine ⟨by show (s.gpr kp).toNat + 128 ≤ _; rw [hP]; exact hf, fun o ho => ⟨_, hwr, ?_⟩, ?_,
      by show (s.gpr .ecx).toNat + 0 ≤ _; omega_using [cn]⟩
    · show Region.Contains _ (addr (s.gpr kp) o) 16
      have ho' : o + 16 ≤ 128 := ho
      rw [hP, addr_eq (by omega_using [hf, ho'])]
      exact Offset.contains_base _ (by omega_using [ho']) (by omega_using [ho'])
    · intro a h₁ _
      simp only [Region.Contains] at h₁
      exact absurd h₁ (by show ¬ _ + 1 ≤ 0; omega_arith)
  have hok := stage_ok
  unfold stageOk at hok
  split at hok <;> [cases hok; rename_i σ hrun]
  simp only [Bool.and_eq_true] at hok
  obtain ⟨co, cin⟩ := hok
  refine runS_wp ok (RelS.init rel rfl) hrun fun s' hr => ⟨hr.gpr, hr.rd, hr.wr, hr.syms, ?_, fun m hm q hq => ?_⟩
  · have := hr.frameIn cin
    rw [show (s.gpr soparams.oreg) = s.gpr kp from rfl, hP, BitVec.add_zero, Nat.sub_zero] at this
    exact this
  · have := hr.out (List.all_eq_true.mp co m (List.mem_range.mpr hm)) hq
    rw [show (s.gpr soparams.oreg) = s.gpr kp from rfl, hP, BV.cst_eval] at this
    exact this

/-- The key at `ecx` to its four words with `FK`, in the rounds' form, and
the mask (`headX`). -/
theorem headX_wp (htb : s.gpr tbr = s.syms tableName) (hK : s.gpr .ecx = K)
    (hin : InRegions (s.rd ++ s.wr) (addr K 0) 16) (hf : K.toNat + 16 ≤ 2 ^ 32) :
    WP isa (.block headX) s fun s' => Same s s' ∧ (∀ q < 16, byte (s'.xmm m0) q = 0x0f#8) ∧
      ∀ w < 4, ∀ q < 16, byte (s'.xmm (xreg w)) q =
        pl (s.mem (K.setWidth 64 + BitVec.ofNat 64 (4 * w + q % 4))) ^^^ byte (tblAt oFK) (4 * w + q % 4) := by
  have rel : Rel hparams (envOf hparams s) Regs.init s :=
    rel_init (p := hparams) htb (by show (s.gpr .ecx).toNat + 16 ≤ _; rw [hK]; exact hf) fun o ho => by
      have e : o = 0 := by have : o + 16 ≤ 16 := ho; omega_using [this]
      subst e
      show InRegions _ (addr (s.gpr .ecx) 0) 16
      rw [hK]; exact hin
  have hok := head_ok
  unfold headOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true] at hok
  obtain ⟨cw, cm⟩ := hok
  refine run_wp rel hrun fun s' hr hsame => ⟨hsame, mask_ok hr cm, fun w hw4 q hq => ?_⟩
  have h := List.all_eq_true.mp cw w (List.mem_range.mpr hw4)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [hr.bytes h.1 q hq, BV.same_eval _ (List.all_eq_true.mp h.2 q (List.mem_range.mpr hq)), AesNiKey.hw, BV.eval,
    mask_zero, cterms_sum, BitVec.zero_xor, env_key hparams (show 4 * w + q % 4 < 16 by omega_using [hw4]),
    show (s.gpr hparams.kreg) = s.gpr .ecx from rfl, hK]
  rfl

/-- The state with `n` turns left, from the words `x₀` the loop starts
with: the pointers after `8 - n` turns, the turns left in `ecx`, the mask,
the words after `4 (8 - n)` rounds in their registers, the rows of
constants of the turns left, and the round keys of the turns done. -/
structure Inv (s₀ : State) (P : BitVec 32) (x₀ : Nat → Word) (n : Nat) (s : State) : Prop where
  le : n ≤ 8
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tb : s.gpr tbr = s₀.syms tableName
  kp : s.gpr kp = P + BitVec.ofNat 32 (16 * (8 - n))
  cnt : s.gpr .ecx = BitVec.ofNat 32 n
  msk : ∀ q < 16, byte (s.xmm m0) q = 0x0f#8
  words : ∀ u < 4, Hw0 (s.xmm (xreg u)) (Proof.Sm4.quads .key Spec.Sm4.ck (8 - n) x₀ u)
  rows : ∀ m, 8 - n ≤ m → m < 8 → ∀ q < 16,
    s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * m + q)) = byte (tblAt (oCK + 16 * m)) q
  done : ∀ m < 8 - n, ∀ q < 16, s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * m + q)) =
    byteAt (Proof.Sm4.quads .key Spec.Sm4.ck (m + 1) x₀ (q / 4)) (3 - q % 4)
  frame : Frame [⟨P.setWidth 64, 128⟩] s₀.mem s.mem

/-- A turn of the loop: four rounds, and their round keys over the turn's row. -/
theorem turn_wp (hwr : (⟨P.setWidth 64, 128⟩ : Region) ∈ s₀.wr) (hf : P.toNat + 128 ≤ 2 ^ 32)
    {x₀ : Nat → Word} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ P x₀ n s) :
    WP isa (.block turn) s fun s' => s'.zf = some (decide (n = 1)) ∧ Inv s₀ P x₀ (n - 1) s' := by
  obtain ⟨m, hm'⟩ : ∃ m, m = 8 - n := ⟨_, rfl⟩
  have hn8 := hI.le
  have hm8 : m < 8 := by omega_using [hn, hm']
  have kp64 : (s.gpr kp).setWidth 64 = P.setWidth 64 + BitVec.ofNat 64 (16 * m) := by
    rw [hI.kp, ← hm']; exact addr_eq (by omega_using [hf, hm8])
  have kpN : (s.gpr kp).toNat = P.toNat + 16 * m := by
    rw [hI.kp, ← hm', Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 16 * m) (by omega_using [hm8]),
      Nat.mod_eq_of_lt (by omega_using [hf, hm8])]
  have ha0 : addr (s.gpr kp) 0 = P.setWidth 64 + BitVec.ofNat 64 (16 * m) := by
    rw [addr_eq (by omega_using [kpN, hf, hm8]), BitVec.add_zero, kp64]
  have he : Env s := ⟨by rw [hI.tb, hI.syms], by omega_using [kpN, hf, hm8],
    ⟨_, List.mem_append_right _ (by rw [hI.wr]; exact hwr), by
      rw [ha0]; exact Offset.contains_base _ (by omega_using [hm8]) (by omega_using [hm8])⟩, hI.msk⟩
  have hrow : ∀ w < 4, ∀ j < 4, kb s (4 * w + j) = pk (byteAt (Spec.Sm4.ck (4 * m + w)) j) := fun w hw j hj => by
    rw [kb, kp64, Offset.add_ofNat_add_ofNat, hI.rows m (by omega_using [hm']) hm8 _ (by omega_using [hw, hj]),
      ck_row hm8 hw hj]
  obtain ⟨x, hx'⟩ : ∃ x, x = Proof.Sm4.quads .key Spec.Sm4.ck m x₀ := ⟨_, rfl⟩
  have hx : ∀ u < 4, Hw0 (s.xmm (xreg u)) (x u) := by rw [hx', hm']; exact hI.words
  show WP isa (.block (round (vr 0) (vr 1) (vr 2) (vr 3) 0 ++ (round (vr 1) (vr 2) (vr 3) (vr 4) 1 ++
    (round (vr 2) (vr 3) (vr 4) (vr 5) 2 ++ (round (vr 3) (vr 4) (vr 5) (vr 6) 3 ++
      (outX ++ Impl.Sm4.X86.AesNiKey.step)))))) s _
  have same_kb : ∀ {t t' : State}, Same t t' → ∀ o, kb t' o = kb t o := fun {t t'} h o => by
    obtain ⟨f, rfl⟩ := h; rfl
  obtain ⟨y₁, hy₁⟩ : ∃ y, y = Proof.Sm4.sround .key (Spec.Sm4.ck (4 * m)) 0 x := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y, y = Proof.Sm4.sround .key (Spec.Sm4.ck (4 * m + 1)) 1 y₁ := ⟨_, rfl⟩
  obtain ⟨y₃, hy₃⟩ : ∃ y, y = Proof.Sm4.sround .key (Spec.Sm4.ck (4 * m + 2)) 2 y₂ := ⟨_, rfl⟩
  refine WP.block_append_iff.mpr (WP.mono (round_ok (w := 0) (x := x) (by decide) he hx (hrow 0 (by decide)))
    fun s₁ ⟨sm₁, m₁, x₁⟩ => ?_)
  rw [show Spec.Sm4.ck (4 * m + 0) = Spec.Sm4.ck (4 * m) from rfl, ← hy₁] at x₁
  have he₁ := he.same sm₁ m₁
  refine WP.block_append_iff.mpr (WP.mono (round_ok (w := 1) (x := y₁)
    (c := Spec.Sm4.ck (4 * m + 1)) (by decide) he₁ x₁
    (fun j hj => by rw [same_kb sm₁]; exact hrow 1 (by decide) j hj)) fun s₂ ⟨sm₂, m₂, x₂⟩ => ?_)
  rw [← hy₂] at x₂
  have s02 := sm₁.trans sm₂
  have he₂ := he.same s02 m₂
  refine WP.block_append_iff.mpr (WP.mono (round_ok (w := 2) (x := y₂)
    (c := Spec.Sm4.ck (4 * m + 2)) (by decide) he₂ x₂
    (fun j hj => by rw [same_kb s02]; exact hrow 2 (by decide) j hj)) fun s₃ ⟨sm₃, m₃, x₃⟩ => ?_)
  rw [← hy₃] at x₃
  have s03 := s02.trans sm₃
  have he₃ := he.same s03 m₃
  refine WP.block_append_iff.mpr (WP.mono (round_ok (w := 3) (x := y₃)
    (c := Spec.Sm4.ck (4 * m + 3)) (by decide) he₃ x₃
    (fun j hj => by rw [same_kb s03]; exact hrow 3 (by decide) j hj)) fun s₄ ⟨sm₄, m₄, x₄⟩ => ?_)
  have s04 := s03.trans sm₄
  have he₄ := he.same s04 m₄
  have x₄' : ∀ u < 4, Hw0 (s₄.xmm (xreg u)) (Proof.Sm4.quads .key Spec.Sm4.ck (m + 1) x₀ u) := by
    rw [show Proof.Sm4.quads .key Spec.Sm4.ck (m + 1) x₀ = Proof.Sm4.quad .key Spec.Sm4.ck m x from by rw [hx']; rfl,
      Proof.Sm4.quad, ← hy₁, ← hy₂, ← hy₃]
    exact x₄
  refine WP.block_append_iff.mpr (WP.mono (out_wp he₄ x₄') fun s₅ ⟨sm₅, o₅, k₅, m₅⟩ => ?_)
  have s05 := s04.trans sm₅
  obtain ⟨f, rfl⟩ := s05
  have hw16 : InRegions s.wr (addr (s.gpr kp) 0) 16 := ⟨_, by rw [hI.wr]; exact hwr, by
    rw [ha0]; exact Offset.contains_base _ (by omega_using [hm8]) (by omega_using [hm8])⟩
  show WP isa (.block (.movdquStore ⟨kp, 0⟩ .xmm4 :: [.alu .add kp (.imm 16), .alu .sub .ecx (.imm 1)]))
    { s with xmm := f } _
  refine wp_stx (s := { s with xmm := f }) hw16 ?_
  refine wp_addi_x fun s₆ u₆ x₆ => wp_subi_x fun s₇ u₇ x₇ z₇ => WP.block_nil ?_
  have e₇ : s₇.mem = s.mem.writeW (addr (s.gpr kp) 0) (f .xmm4) := by rw [u₇.mem, u₆.mem]
  have xe : s₇.xmm = f := by rw [x₇, x₆]
  have c₆ : s₆.gpr .ecx = BitVec.ofNat 32 n := by rw [u₆.other _ (by decide)]; exact hI.cnt
  have fr : Frame [⟨P.setWidth 64 + BitVec.ofNat 64 (16 * m), 16⟩] s.mem s₇.mem := by
    rw [e₇, ha0]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 16)
  have keep : ∀ m' < 8, m' ≠ m → ∀ q < 16, s₇.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * m' + q)) =
      s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * m' + q)) := fun m' hm'8 hne q hq => by
    have := fr.bytes (R := ⟨P.setWidth 64 + BitVec.ofNat 64 (16 * m' + q), 1⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega_using [hne, hq]) (by omega_using [hm'8, hq]) (by omega_using [hm8]))
      (show (1 : Nat) ≤ 2 ^ 64 by decide) (i := 0) (show (0 : Nat) < 1 by decide)
    rw [BitVec.add_zero] at this
    exact this
  have new : ∀ q < 16, s₇.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * m + q)) =
      byteAt (Proof.Sm4.quads .key Spec.Sm4.ck (m + 1) x₀ (q / 4)) (3 - q % 4) := fun q hq => by
    rw [e₇, ha0, ← Offset.add_ofNat_add_ofNat,
      ← byte_readW ((s.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 (16 * m)) (f .xmm4)))
        (P.setWidth 64 + BitVec.ofNat 64 (16 * m)) (w := 128) (k := q) (by omega_using [hq]),
      Mem.readW_writeW_self _ _ 16 _ (by decide)]
    exact o₅ q hq
  have e8 : 8 - (n - 1) = m + 1 := by omega_using [hn, hm', hn8]
  refine ⟨?_, by omega_using [hn8], fun r h1 h2 h3 => ?_, by rw [u₇.rd, u₆.rd]; exact hI.rd,
    by rw [u₇.wr, u₆.wr]; exact hI.wr, by rw [u₇.syms, u₆.syms]; exact hI.syms, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [z₇, c₆, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Wp.sub_beq (by omega_using [hn8]) (by decide)]
  · rw [u₇.other _ h2, u₆.other _ h3]; exact hI.gpr r h1 h2 h3
  · rw [u₇.other _ (by decide), u₆.other _ (by decide)]; exact hI.tb
  · rw [e8, u₇.other _ (by decide), u₆.gpr]
    show s.gpr kp + 16 = _
    rw [hI.kp, ← hm', show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_ofNat_add_ofNat]
    congr 2
  · rw [u₇.gpr, c₆]; exact Wp.ofNat_pred hn
  · rw [xe]; exact m₅
  · intro u hu q hq
    rw [e8, xe, k₅ u hu q (by omega_using [hq])]
    exact x₄' u hu q hq
  · intro m' h1 h2 q hq
    rw [e8] at h1
    rw [keep m' h2 (by omega_using [h1]) q hq]
    exact hI.rows m' (by omega_using [h1, hm']) h2 q hq
  · intro m' h1 q hq
    rw [e8] at h1
    by_cases hmm : m' = m
    · subst hmm; exact new q hq
    · rw [keep m' (by omega_using [h1, hm8]) hmm q hq]
      exact hI.done m' (by omega_using [h1, hmm, hm']) q hq
  · exact hI.frame.trans (fr.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [hm8])⟩)

/-- The eight turns. -/
theorem loop_wp (hwr : (⟨P.setWidth 64, 128⟩ : Region) ∈ s₀.wr) (hf : P.toNat + 128 ≤ 2 ^ 32)
    {x₀ : Nat → Word} {n : Nat} (hn : 1 ≤ n) (hI : Inv s₀ P x₀ n s) :
    WP isa (.loop (.block turn) .ne) s (Inv s₀ P x₀ 0) := by
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ Inv s₀ P x₀ n s) ?_ n s ⟨hn, hI⟩
  rintro n s ⟨hn, hI⟩
  refine WP.mono (turn_wp hwr hf hn hI) fun s₁ ⟨z₁, i₁⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show s₁.zf.map _ = _; rw [z₁]; rfl, i₁⟩
  · exact .inr ⟨by show s₁.zf.map _ = _; rw [z₁, decide_eq_false h1]; rfl, n - 1, by omega_using [hn],
      by omega_using [hn, h1], i₁⟩

end

/-! ## The function -/

section
variable {s : State}

/-- The table's row of `FK`. -/
theorem fk_row {w j : Nat} (hw : w < 4) (hj : j < 4) :
    byte (tblAt oFK) (4 * w + j) = pl (byteAt (Spec.Sm4.fk.getD w 0) j) := by
  have h := List.all_eq_true.mp consts_all.1 w (List.mem_range.mpr hw)
  have h := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [beq_iff_eq] at h
  exact h

/-- The schedule's address, the constants, the key's words and the eight
turns (`head`), from the state after the table's address is taken: the
loop's invariant with eight turns left. -/
theorem head_wp {P K : BitVec 32} {key : Spec.Sm4.Block} (htb : s.gpr tbr = s.syms tableName)
    (hin1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * 1)) 4)
    (hP : s.mem.readW (addr (s.gpr .esp) (4 + 4 * 1)) 32 = P)
    (hin0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * 0)) 4)
    (hK : s.mem.readW (addr (s.gpr .esp) (4 + 4 * 0)) 32 = K)
    (hwr : (⟨P.setWidth 64, 128⟩ : Region) ∈ s.wr) (hfP : P.toNat + 128 ≤ 2 ^ 32)
    (hAS : Region.Disjoint ⟨addr (s.gpr .esp) (4 + 4 * 0), 4⟩ ⟨P.setWidth 64, 128⟩)
    (hinK : InRegions (s.rd ++ s.wr) (addr K 0) 16) (hfK : K.toNat + 16 ≤ 2 ^ 32)
    (dKS : Region.Disjoint ⟨K.setWidth 64, 16⟩ ⟨P.setWidth 64, 128⟩)
    (hkey : ∀ i < 16, s.mem (K.setWidth 64 + BitVec.ofNat 64 i) = key.getD i 0) :
    WP isa (.block head) s (Inv s P (Proof.Sm4.keyInit key) 8) := by
  show WP isa (.block (.mov kp (.mem ⟨.esp, 4 + 4 * 1⟩) :: (stage ++ (.mov .ecx (.mem ⟨.esp, 4 + 4 * 0⟩) ::
    (headX ++ [.mov .ecx (.imm 8)]))))) s _
  refine Wp.wp_ldm (B := s.gpr .esp) rfl hin1 fun s₂ u₂ => ?_
  have p₂ : s₂.gpr kp = P := u₂.gpr.trans hP
  refine WP.block_append_iff.mpr (WP.mono (stage_wp (P := P) (by rw [u₂.other _ (by decide), u₂.syms]; exact htb) p₂
    (by rw [u₂.wr]; exact hwr) hfP) fun s₃ ⟨g₃, rd₃, wr₃, sy₃, f₃, rows₃⟩ => ?_)
  have f₃' : Frame [⟨P.setWidth 64, 128⟩] s.mem s₃.mem := by rw [← u₂.mem]; exact f₃
  have k₃ : s₃.mem.readW (addr (s.gpr .esp) (4 + 4 * 0)) 32 = K := by
    rw [f₃'.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hAS) (by decide), hK]
  refine Wp.wp_ldm (B := s.gpr .esp) (by rw [g₃, u₂.other _ (by decide)])
    (by rw [rd₃, wr₃, u₂.rd, u₂.wr]; exact hin0) fun s₄ u₄ => ?_
  have c₄ : s₄.gpr .ecx = K := u₄.gpr.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (headX_wp (K := K)
    (by rw [u₄.other _ (by decide), u₄.syms, g₃, sy₃, u₂.other _ (by decide), u₂.syms]; exact htb) c₄
    (by rw [u₄.rd, u₄.wr, rd₃, wr₃, u₂.rd, u₂.wr]; exact hinK) hfK) fun s₅ ⟨sm₅, m₅, w₅⟩ => ?_)
  obtain ⟨f, rfl⟩ := sm₅
  refine wp_movi_x fun s₆ u₆ x₆ => WP.block_nil ?_
  have e₆ : s₆.mem = s₃.mem := by rw [u₆.mem]; exact u₄.mem
  have keyb : ∀ i < 16, s₄.mem (K.setWidth 64 + BitVec.ofNat 64 i) = key.getD i 0 := fun i hi => by
    rw [u₄.mem, f₃'.bytes (R := ⟨K.setWidth 64, 16⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact dKS) (show (16 : Nat) ≤ 2 ^ 64 by decide) hi]
    exact hkey i hi
  refine ⟨Nat.le_refl _, fun r h1 h2 h3 => ?_, by rw [u₆.rd]; exact u₄.rd.trans (rd₃.trans u₂.rd),
    by rw [u₆.wr]; exact u₄.wr.trans (wr₃.trans u₂.wr), by rw [u₆.syms]; exact u₄.syms.trans (sy₃.trans u₂.syms),
    ?_, ?_, ?_, by rw [x₆]; exact m₅, fun u hu q hq => ?_, fun m _ hm q hq => by rw [e₆]; exact rows₃ m hm q hq,
    fun m hm => absurd hm (Nat.not_lt_zero m), by rw [e₆]; exact f₃'⟩
  · rw [u₆.other _ h2]
    show s₄.gpr r = _
    rw [u₄.other _ h2, g₃, u₂.other _ h3]
  · rw [u₆.other _ (by decide)]
    show s₄.gpr tbr = _
    rw [u₄.other _ (by decide), g₃, u₂.other _ (by decide)]; exact htb
  · rw [u₆.other _ (by decide)]
    show s₄.gpr kp = _
    rw [u₄.other _ (by decide), g₃, p₂]
    exact (BitVec.add_zero P).symm
  · rw [u₆.gpr]; rfl
  · rw [x₆]
    show byte (f (xreg u)) q = pl (byteAt (Proof.Sm4.keyInit key u) q)
    rw [w₅ u hu q (by omega_using [hq]), Nat.mod_eq_of_lt hq, keyb _ (by omega_using [hu, hq]), fk_row hu hq,
      Proof.Sm4.keyInit, byteAt_xor, pl_xor, byteAt_wordAt _ _ hq]

/-- `expandKey`'s precondition, with `n` bytes of stack below `esp`, at
least four: the key and the two argument slots readable, the schedule
writable, apart from them, from the return address and from that stack. -/
structure KPre (n : Nat) (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 16⟩, ⟨argAddr s 0, 8⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64, 128⟩]
  dKS : Region.Disjoint ⟨(arg s 0).setWidth 64, 16⟩ ⟨(arg s 1).setWidth 64, 128⟩
  dAS : Region.Disjoint ⟨argAddr s 0, 8⟩ ⟨(arg s 1).setWidth 64, 128⟩
  dRS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 128⟩
  bK : Region.Disjoint (below (s.gpr .esp) n) ⟨(arg s 0).setWidth 64, 16⟩
  bS : Region.Disjoint (below (s.gpr .esp) n) ⟨(arg s 1).setWidth 64, 128⟩
  fK : (arg s 0).toNat + 16 ≤ 2 ^ 32
  fS : (arg s 1).toNat + 128 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  sp : n ≤ (s.gpr .esp).toNat
  n4 : 4 ≤ n

/-- The key schedule on x86, with `n` bytes of stack. -/
def keyX (n : Nat) : Contract isa where
  pre := KPre n
  post s s' := Spec.Sm4.scheduleAt s'.mem ((arg s 1).setWidth 64) =
    Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 2, arg s₁ i = arg s₂ i

theorem argAddr_off (s : State) {j : Nat} (hf : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32) (hj : j < 2) :
    argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * j) := by
  show addr (s.gpr .esp) (4 + 4 * j) = _
  rw [addr_eq (by omega_using [hf, hj]), Offset.add_ofNat_add_ofNat]

/-- `expandKey` writes the schedule of the key. -/
theorem expandKey_wp {n : Nat} (h : KPre n s) :
    WP isa expandKey s fun s' => abiPreserved s s' ∧ (keyX n).post s s' := by
  have hsp4 : 4 ≤ (s.gpr .esp).toNat := Nat.le_trans h.n4 h.sp
  have hfSp := h.fSp
  have b4 : Region.Sub (below (s.gpr .esp) 4) (below (s.gpr .esp) n) := VG.X86.below_sub h.n4 h.sp
  have a0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := by
    rw [argAddr_off s hfSp (by decide), BitVec.add_zero]
  have inA : ∀ j < 2, InRegions (s.rd ++ s.wr) (argAddr s j) 4 := fun j hj =>
    ⟨⟨argAddr s 0, 8⟩, by rw [h.rd]; simp, by
      rw [argAddr_off s hfSp hj, a0]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  have subA : Region.Sub ⟨argAddr s 0, 4⟩ ⟨argAddr s 0, 8⟩ := Region.sub_prefix (by decide)
  have hinK : InRegions (s.rd ++ s.wr) (addr (arg s 0) 0) 16 := ⟨⟨(arg s 0).setWidth 64, 16⟩, by rw [h.rd]; simp, by
    rw [addr_eq (by omega_using [h.fK]), BitVec.add_zero]; exact Region.contains_self _ 16⟩
  show WP isa (.seq (.frame (.symPush .eax tableName) (.block []) (.pop .ecx 1)) (.seq (.block head)
    (.loop (.block turn) .ne))) s _
  refine WP.seq (WP.mono (symFrame_ok tableName s hsp4) fun s₁ a₁ => ?_)
  have esp₁ : s₁.gpr .esp = s.gpr .esp := a₁.gpr .esp (by decide)
  have arg₁ : ∀ j < 2, s₁.mem.readW (argAddr s j) 32 = arg s j := fun j hj => by
    have := a₁.arg (j := j) hsp4 (by omega_using [hfSp, hj])
    simp only [VG.X86.arg, VG.X86.argAddr, esp₁] at this
    exact this
  have key₁ : ∀ i < 16, s₁.mem ((arg s 0).setWidth 64 + BitVec.ofNat 64 i) =
      (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64)).getD i 0 := fun i hi => by
    rw [a₁.frame.bytes (R := ⟨(arg s 0).setWidth 64, 16⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (h.bK.sub_left b4).symm) (show (16 : Nat) ≤ 2 ^ 64 by decide) hi,
      blockAt_getD _ _ hi]
  refine WP.seq (WP.mono (head_wp (P := arg s 1) (K := arg s 0)
    (key := Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64)) (by show s₁.gpr .eax = _; rw [a₁.addr, a₁.syms])
    (by rw [esp₁, a₁.rd, a₁.wr]; exact inA 1 (by decide)) (by rw [esp₁]; exact arg₁ 1 (by decide))
    (by rw [esp₁, a₁.rd, a₁.wr]; exact inA 0 (by decide)) (by rw [esp₁]; exact arg₁ 0 (by decide))
    (by rw [a₁.wr, h.wr]; exact List.mem_singleton_self _) h.fS
    (by rw [esp₁]; exact h.dAS.sub_left subA) (by rw [a₁.rd, a₁.wr]; exact hinK) h.fK h.dKS key₁)
    fun s₂ hI₂ => ?_)
  refine WP.mono (loop_wp (by rw [a₁.wr, h.wr]; exact List.mem_singleton_self _) h.fS (by decide) hI₂)
    fun s₃ hI => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have h1 : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
    have h2 : r ≠ .ecx := by rintro rfl; simp [calleeSaved] at hr
    have h3 : r ≠ .edx := by rintro rfl; simp [calleeSaved] at hr
    rw [hI.gpr r h1 h2 h3]
    exact a₁.gpr r (by simp [h1, h2])
  · rw [hI.frame.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.dRS) (by decide)]
    exact a₁.ret hsp4 (by omega_using [hfSp])
  · show Spec.Sm4.scheduleAt s₃.mem ((arg s 1).setWidth 64) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem ((arg s 0).setWidth 64))
    rw [Proof.Sm4.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [Vector.getElem_ofFn]
    apply word_ext
    intro k hk
    have hd := hI.done (i / 4) (by omega_using [hi]) (4 * (i % 4) + (3 - k)) (by omega_arith)
    rw [show 16 * (i / 4) + (4 * (i % 4) + (3 - k)) = 4 * i + (3 - k) by omega_arith,
      show (4 * (i % 4) + (3 - k)) / 4 = i % 4 by omega_using [hk],
      show 3 - (4 * (i % 4) + (3 - k)) % 4 = k by omega_using [hk]] at hd
    rw [byteAt_sched _ _ hi hk, hd]
    rfl

end

/-! ## Constant time -/

/-- The initial taint: `esp` public, the argument word holding `schedule`
the base address of the writable region, and four bytes of stack. -/
def keyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128], argLen := 12, argBases := [(8, 0)], room := 4 }

theorem keyTaint_wf {n : Nat} {s : State} (h : KPre n s) : VG.X86.Taint.Wf keyTaint s := by
  have hsp4 : 4 ≤ (s.gpr .esp).toNat := Nat.le_trans h.n4 h.sp
  have hfSp := h.fSp
  have hfS := h.fS
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [keyTaint]; omega_using [hfSp], ?_⟩, ?_⟩ fun _ => ⟨hsp4, ?_⟩
  · rw [h.wr]
    exact .cons (Nat.le_refl _) .nil
  · rw [h.wr]
    exact List.pairwise_singleton _ _
  · simp only [h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    simp only [BitVec.toNat_setWidth]
    omega_using [hfS]
  · simp only [h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 8) (by omega_using [hfSp]) h.dRS h.dAS
  · intro p hp'
    simp only [keyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, h.wr, addr, arg, argAddr]
  · intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth hsp4).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ : Region).Disjoint r
    rw [e]
    simp only [h.wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact h.bS.sub_left (VG.X86.below_sub h.n4 h.sp)

theorem keyTaint_agree {n : Nat} {s₁ s₂ : State} (h₁ : KPre n s₁) (h₂ : KPre n s₂)
    (hpub : (keyX n).pub s₁ s₂) : VG.X86.Taint.Agree keyTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have f₁ := h₁.fSp
  have f₂ := h₂.fSp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, keyTaint_wf h₁, keyTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp, fun k h4 hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [h₁.wr, h₂.wr, ha 1 (by decide)]
  · simp only [keyTaint] at hk
    rw [show VG.X86.Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 12) f₁ h4 hk, VG.X86.Taint.argByte_eq (n := 12) f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha _ (by omega_using [hk]))

theorem expandKey_ct (n : Nat) : ConstantTime isa (keyX n).pre (keyX n).pub expandKey :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) keyTaint (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contract of `Spec/` -/

/-- `KPre n`, from what `sig_pre` leaves of the precondition of
`Spec.Sm4.expandKeyContract X86.abi n` for a numeral `n`. -/
theorem KPre.of_sig {n : Nat} {s : State} (n4 : 4 ≤ n)
    (h : n ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 8 ≤ 2 ^ 32 ∧
      s.rd = [⟨(arg s 0).setWidth 64, 16⟩, ⟨argAddr s 0, 8⟩] ∧ s.wr = [⟨(arg s 1).setWidth 64, 128⟩] ∧
      Region.Disjoint ⟨(arg s 0).setWidth 64, 16⟩ ⟨(arg s 1).setWidth 64, 128⟩ ∧
      Region.Disjoint ⟨(arg s 1).setWidth 64, 128⟩ ⟨argAddr s 0, 8⟩ ∧
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 0).setWidth 64, 16⟩ ∧
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 128⟩ ∧
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨argAddr s 0, 8⟩ ∧
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n, n⟩ ⟨(arg s 0).setWidth 64, 16⟩ ∧
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n, n⟩ ⟨(arg s 1).setWidth 64, 128⟩ ∧
      Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n, n⟩ ⟨argAddr s 0, 8⟩ ∧
      (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 ≤ 2 ^ 32) : KPre n s := by
  obtain ⟨hn, hsp, hrd, hwr, dKS, dSA, -, dRS, -, bK, bS, -, fK, fS⟩ := h
  have be : below (s.gpr .esp) n = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n, n⟩ := by
    simp only [below, Taint.sub_setWidth hn]
  exact ⟨hrd, hwr, dKS, dSA.symm, dRS, be ▸ bK, be ▸ bS, fK, fS, hsp, hn, n4⟩

/-- `keyX n` implies the contract of `Spec/`, given its precondition's facts. -/
theorem key_implies {n : Nat} (hpre : ∀ s, (Spec.Sm4.expandKeyContract X86.abi n).pre s → KPre n s)
    (hsat : ∃ s, (Spec.Sm4.expandKeyContract X86.abi n).pre s) :
    (keyX n).Implies (Spec.Sm4.expandKeyContract X86.abi n) where
  pre := hpre
  post := by
    intro s t _ h
    sig_post [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun i hi => ?_⟩
    rcases (show i = 0 ∨ i = 1 by omega_using [hi]) with rfl | rfl
    · exact h0
    · exact h1
  sat := hsat

theorem key_sat4 : ∃ s, (Spec.Sm4.expandKeyContract X86.abi 4).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] [Proof.Sm4.X86.expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using Proof.Sm4.X86.expandKeyFrameSat

/-- The key schedule meets `Spec.Sm4.expandKeyContract` with four bytes of stack. -/
theorem expandKey_verified :
    Verified X86.target Impl.Sm4.X86.AesNiKey.expandKey (Spec.Sm4.expandKeyContract X86.abi 4) :=
  Verified.of_correct (fun _ h => expandKey_wp h) (expandKey_ct 4) (key_implies (fun s h => by
    sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      stackBelow] at h
    exact KPre.of_sig (by decide) h) key_sat4)

/-- And with the 1448 bytes that `vg_sm4_gcm_init` leaves its key schedule. -/
theorem expandKey_verifiedK :
    Verified X86.target Impl.Sm4.X86.AesNiKey.expandKey (Spec.Sm4.expandKeyContract X86.abi 1448) :=
  Verified.of_correct (fun _ h => expandKey_wp h) (expandKey_ct 1448) (key_implies (fun s h => by
    sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      stackBelow] at h
    exact KPre.of_sig (by decide) h) Proof.Sm4.X86.expandKeyFrameSat_pre)

/-! ## Without secret residue -/

section
open VG.X86.Scrub

/-- The postcondition reads the memory on return only within the buffers. -/
theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Sm4.expandKeyContract X86.abi stack) (Spec.Sm4.expandKeySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm4.expandKeyPostOut_local _)

/-- `Spec.Sm4.expandKeyApi` as emitted (`Impl.Sm4.X86.AesNiKey.Fn.expandKey`) meets its contract in
constant time and returns without secret residue: the residue analysis (`X86.rtaint`) finds no
doubleword of the stack to zero, and the cleanup clears the registers. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Sm4.X86.AesNiKey.Fn.expandKey (Spec.Sm4.expandKeyContract X86.abi 4) 0 :=
  verifiedScrubbedSel (api := Spec.Sm4.expandKeyApi) (W := 4)
    { code := Impl.Sm4.X86.AesNiKey.expandKey
      verified := expandKey_verified }
    Impl.Sm4.X86.AesNiKey.Fn.noWords (expandKeyOut _) (by decide) ⟨_, by taint_decide_ct⟩

end

end VG.Proof.Sm4.X86.AesNiKey
