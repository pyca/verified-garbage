module

public import VerifiedGarbage.Impl.AesXts.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.AesXts.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Vec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Vec
import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
import VerifiedGarbage.Proof.AesXts.Alpha
meta import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Impl.AesXts.PPC64LE
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.AesXts.PPC64LE.Body
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
meta import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-!
# XTS-AES on PPC64LE: the contracts

`Verified` for `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`: AES-CBC's
`batched_wp` and `batched_ct` (`Proof/AesCbc/PPC64LE/`) with the bodies of
`Body.lean` and the groups of eight blocks proven here (`vgroup_ok`: the
tweaks doubled in two words and saved in the slots, then the blocks in
vector registers through `Proof/Aes/PPC64LE/Crypto/`'s rounds), and the
contracts of `Spec/Xts/Contract.lean` from `modePPC64LE (xtsMode enc)`.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LE
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.PPC64LE
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes copyMem copyMem_frame copyMem_bytes aesWith_state
  aesInvWith_state)
open VG.Impl.AesCbc.PPC64LE (slot advance8 vsetup)
open VG.Spec.Aes (bytesAt)

/-! ## Eight blocks at a time -/

/-- XTS extends its output one block at a time. -/
theorem xts_steps (enc : Bool) :
    Steps (AesXts.xtsMode enc) fun R w x c => Spec.Xts.block (ciphOf enc R w) c x := by
  intro R w t xs x
  simp only [AesXts.xtsMode_out, AesXts.xtsMode_chain, AesXts.crypt_snoc]

/-- The tweak after block `i` is the one before it times `α`. -/
theorem xts_chain (enc : Bool) (s₀ : State) {i : Nat} (hi : i < N s₀) :
    chainK (AesXts.xtsMode enc) s₀ (i + 1) = Spec.Xts.mulAlpha (chainK (AesXts.xtsMode enc) s₀ i) := by
  have hlt : ((blks s₀).take i).length = i := by simp [Spec.Cbc.blocksAt]; omega
  simp only [chainK, AesXts.xtsMode_chain, take_succ_blkOf s₀ hi, List.length_append, List.length_singleton,
    hlt, AesXts.next_succ]

/-! ## The tweak in two words -/

/-- The 16 bytes of the words `a` (bytes 0–7) and `b` (8–15), little-endian. -/
def wb (a b : BitVec 64) : List Byte :=
  (List.range 8).map (fun j => a.extractLsb' (8 * j) 8) ++ (List.range 8).map (fun j => b.extractLsb' (8 * j) 8)

theorem bytes_pair (m : Mem) (P : Addr) (a b : BitVec 64) :
    bytesAt ((m.writeW P a).writeW (P + BitVec.ofNat 64 8) b) P 16 = wb a b := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesXts.bytesAt_append,
    AesXts.bytesAt_writeW_below _ _ _ (a := 8) (n := 8) (by decide) (by decide),
    AesXts.bytesAt_writeW (k := 8) _ _ _ (by decide), AesXts.bytesAt_writeW (k := 8) _ _ _ (by decide)]
  rfl

theorem bytes_read (m : Mem) (P : Addr) :
    bytesAt m P 16 = wb (m.readW P 64) (m.readW (P + BitVec.ofNat 64 8) 64) := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesXts.bytesAt_append, AesXts.bytesAt_readW (k := 8),
    AesXts.bytesAt_readW (k := 8)]
  rfl

/-- The low word of the tweak times `α`. -/
abbrev aLo (a b : BitVec 64) : BitVec 64 := (a <<< 1) ^^^ (if b.msb then (0x87 : BitVec 64) else 0)
/-- The high word of the tweak times `α`. -/
abbrev aHi (a b : BitVec 64) : BitVec 64 := (b <<< 1) ||| (if a.msb then (1 : BitVec 64) else 0)

theorem wb_alpha (a b : BitVec 64) : wb (aLo a b) (aHi a b) = Spec.Xts.mulAlpha (wb a b) := by
  let P : Addr := 0
  let m : Mem := (Mem.writeW (fun _ => 0) P a).writeW (P + BitVec.ofNat 64 8) b
  have ha : m.readW P 64 = a := by
    simp only [m]
    rw [Mem.readW_writeW_sep (Offset.sep_base P (n := 8) (e := 8) (k := 8) (by decide) (by decide))
      (by decide), Mem.readW_writeW_self64]
  have hb : m.readW (P + BitVec.ofNat 64 8) 64 = b := Mem.readW_writeW_self64 _ _ _
  have e := AesXts.mulAlpha_words64 m P
  rw [ha, hb, bytes_pair, bytes_pair] at e
  exact e

/-- `dbl`: the tweak in `r9` and `r10` times `α`. -/
theorem dbl_wp {s : State} {rest : List Instr} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r9 = aLo (s.gpr .r9) (s.gpr .r10) → s'.gpr .r10 = aHi (s.gpr .r9) (s.gpr .r10) →
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (dbl ++ rest)) s Φ := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => ?_
  refine wp_li (by decide) fun s₆ u₆ => wp_and fun s₇ u₇ => ?_
  refine wp_lsr (by decide) fun s₈ u₈ => wp_lsl (by decide) fun s₉ u₉ => wp_xor fun s₁₀ u₁₀ => ?_
  refine wp_lsl (by decide) fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => ?_
  refine k s₁₂ ?_ ?_ (fun r h9 h10 h11 h12 => ?_) ?_ ?_ ?_
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₉.other .r11 (by decide),
      u₈.other .r9 (by decide), u₈.other .r11 (by decide), u₇.gpr, u₇.other .r9 (by decide), u₆.gpr,
      u₆.other .r11 (by decide), u₆.other .r9 (by decide), u₅.gpr, u₅.other .r9 (by decide), u₄.gpr,
      u₄.other .r11 (by decide), u₄.other .r9 (by decide), u₃.gpr, u₃.other .r9 (by decide), mask_87]
  · rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other .r12 (by decide), u₁₀.other .r10 (by decide), u₁₀.other .r12 (by decide),
      u₉.other .r10 (by decide), u₉.other .r12 (by decide), u₈.gpr, u₈.other .r10 (by decide),
      u₇.other .r10 (by decide), u₇.other .r9 (by decide), u₆.other .r10 (by decide),
      u₆.other .r9 (by decide), u₅.other .r10 (by decide), u₅.other .r9 (by decide), u₄.other .r10 (by decide),
      u₄.other .r9 (by decide), u₃.other .r10 (by decide), u₃.other .r9 (by decide), ushr63]
  · rw [u₁₂.other _ h10, u₁₁.other _ h10, u₁₀.other _ h9, u₉.other _ h9, u₈.other _ h12,
      u₇.other _ h11, u₆.other _ h12, u₅.other _ h11, u₄.other _ h12, u₃.other _ h11]
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  · rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]
  · rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]

/-! ## The tweaks of a group, in registers -/

/-- The two stores of a tweak at `P` change only its 16 bytes. -/
theorem pair_frame (m : Mem) (P : Addr) (a b : BitVec 64) :
    Frame [⟨P, 16⟩] m ((m.writeW P a).writeW (P + BitVec.ofNat 64 8) b) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base P (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base P (d := 8) (n := 8) (k := 16) (by decide) (by decide))

/-- After the tweaks of the first `m` blocks of a group, computed in `r9`
and `r10`. -/
structure TJ (enc : Bool) (s₀ : State) (k m : Nat) (s t : State) : Prop where
  g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨S s₀, 144⟩] s.mem t.mem
  slot : ∀ j < m, bytesAt t.mem (sl s₀ j) 16 = chainK (AesXts.xtsMode enc) s₀ (k + j)
  w : wb (t.gpr .r9) (t.gpr .r10) = chainK (AesXts.xtsMode enc) s₀ (k + m)

theorem tweakRegs_wp (enc : Bool) {s₀ : State} {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (hW₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀]) (hS : s.gpr .r19 = S s₀)
    (h0 : wb (s.gpr .r9) (s.gpr .r10) = chainK (AesXts.xtsMode enc) s₀ k)
    (m : Nat) (hm : m ≤ 8) {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ t, TJ enc s₀ k m s t → WP isa (.block rest) t Φ) :
    WP isa (.block ((List.range m).flatMap tweakReg ++ rest)) s Φ := by
  induction m generalizing rest Φ with
  | zero =>
    exact cont s ⟨fun _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _),
      by simpa using h0⟩
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]
    refine ih (by omega) fun t ht => ?_
    have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [ht.wr, hW₀]
    have r19 : t.gpr .r19 = S s₀ := by rw [ht.g _ (by decide) (by decide) (by decide) (by decide), hS]
    simp only [tweakReg, List.cons_append, List.nil_append]
    refine wp_std (a := sl s₀ m) (by decide) ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩
      (by rw [r19]) (by rw [hW]; exact in_rw (by simp) (cSl s₀ (by omega))) fun t₁ u₁ => ?_
    refine wp_std (a := sl s₀ m + BitVec.ofNat 64 8) (by decide)
      ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩
      (by rw [u₁.gpr, r19, sl8]) (by rw [u₁.wr, hW]; exact in_rw (by simp) (cSl8 s₀ (by omega)))
      fun t₂ u₂ => ?_
    have hm₂ : t₂.mem = (t.mem.writeW (sl s₀ m) (t.gpr .r9)).writeW (sl s₀ m + BitVec.ofNat 64 8)
        (t.gpr .r10) := by rw [u₂.mem, u₁.mem, u₁.gpr]
    refine dbl_wp fun t₃ g9 g10 g₃ mem₃ rd₃ wr₃ => cont t₃ ?_
    refine ⟨fun r h9 h10 h11 h12 => ?_, by rw [rd₃, u₂.rd, u₁.rd, ht.rd], by rw [wr₃, u₂.wr, u₁.wr, ht.wr],
      ?_, fun j hj => ?_, ?_⟩
    · rw [g₃ r h9 h10 h11 h12, u₂.gpr, u₁.gpr, ht.g r h9 h10 h11 h12]
    · rw [mem₃, hm₂]
      exact ht.frame.trans ((pair_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sl_sub s₀ (by omega)⟩)
    · rw [mem₃, hm₂]
      by_cases hjm : j < m
      · rw [bytesAt_frame (pair_frame _ _ _ _) (one_disj (dSS s₀ (by omega) (by omega) (by omega)))
          (by decide), ht.slot j hjm]
      · have : j = m := by omega
        subst this
        rw [bytes_pair, ht.w]
    · rw [g9, g10, u₂.gpr, u₁.gpr, wb_alpha, ht.w, ← Nat.add_assoc, xts_chain enc s₀ (by omega)]

/-- The tweaks of the eight blocks of a group in slots 0–7, and the next one
at `Iv`. -/
structure TW (enc : Bool) (s₀ : State) (k : Nat) (s t : State) : Prop where
  g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [ivR s₀, ⟨S s₀, 144⟩] s.mem t.mem
  slot : ∀ j < 8, bytesAt t.mem (sl s₀ j) 16 = chainK (AesXts.xtsMode enc) s₀ (k + j)
  iv : bytesAt t.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ (k + 8)

theorem tweaks8_wp (enc : Bool) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (h : LInv (AesXts.xtsMode enc) s₀ k s) {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ t, TW enc s₀ k s t → WP isa (.block rest) t Φ) :
    WP isa (.block (tweaks8 ++ rest)) s Φ := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := h.regs hp
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := h.wrs hp
  simp only [tweaks8, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ld (a := Iv s₀) (by decide) (by decide) (by rw [h.r16, ofNat_zero_add])
    (by rw [hR]; exact in_rw (by simp) cIv0) fun t₁ u₁ => ?_
  refine wp_ld (a := Iv s₀ + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₁.other _ (by decide), h.r16])
    (by rw [u₁.rd, u₁.wr, hR]; exact in_rw (by simp) cIv8) fun t₂ u₂ => ?_
  have w₂ : wb (t₂.gpr .r9) (t₂.gpr .r10) = chainK (AesXts.xtsMode enc) s₀ k := by
    rw [u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, ← bytes_read, h.iv]
  refine tweakRegs_wp enc hk (by rw [u₂.wr, u₁.wr, hW]) (by rw [u₂.other _ (by decide),
    u₁.other _ (by decide), h.r19]) w₂ 8 (by decide) fun t₃ ht => ?_
  have r16 : t₃.gpr .r16 = Iv s₀ := by
    rw [ht.g _ (by decide) (by decide) (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.r16]
  have hW₃ : t₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [ht.wr, u₂.wr, u₁.wr, hW]
  refine wp_std (a := Iv s₀) (by decide) (by decide) (by rw [r16, ofNat_zero_add])
    (by rw [hW₃]; exact in_rw (by simp) cIv0) fun t₄ u₄ => ?_
  refine wp_std (a := Iv s₀ + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₄.gpr, r16])
    (by rw [u₄.wr, hW₃]; exact in_rw (by simp) cIv8) fun t₅ u₅ => cont t₅ ?_
  have hm₅ : t₅.mem = (t₃.mem.writeW (Iv s₀) (t₃.gpr .r9)).writeW (Iv s₀ + BitVec.ofNat 64 8)
      (t₃.gpr .r10) := by rw [u₅.mem, u₄.mem, u₄.gpr]
  have hm₂ : t₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨fun r h9 h10 h11 h12 => ?_, by rw [u₅.rd, u₄.rd, ht.rd, u₂.rd, u₁.rd],
    by rw [u₅.wr, u₄.wr, ht.wr, u₂.wr, u₁.wr], ?_, fun j hj => ?_, ?_⟩
  · rw [u₅.gpr, u₄.gpr, ht.g r h9 h10 h11 h12, u₂.other _ h10, u₁.other _ h9]
  · rw [hm₅, ← hm₂]
    refine (ht.frame.sub fun r hr => ?_).trans ((pair_frame _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩
  · rw [hm₅, bytesAt_frame (pair_frame _ _ _ _) (one_disj (hp.dIS (by omega)).symm) (by decide), ht.slot j hj]
  · rw [hm₅, bytes_pair, ht.w]

/-! ## The eight blocks in vector registers -/

section Vec
open VG.Proof.Aes.PPC64LE.Crypto (Local Inputs aesState result schedule BatchRead readValue Stored
  batchFacts breg_mem breg_ne load_state aesState_byte exec_flip)
open VG.Impl.Aes.PPC64LE.Crypto (breg batchRegs key mask byteMask)

/-- A block of XTS from the vectors: `x` the block, `c` its tweak. -/
theorem xts_vec (enc : Bool) (R : Nat) (w : List Byte) (m : Mem) (P Q : Addr) (res : BitVec 128)
    (hres : aesState res = result (!enc) R w
      (aesState (rev128 (m.read P 16) ^^^ rev128 (m.read Q 16)))) :
    (aesState (res ^^^ rev128 (m.read Q 16))).toList =
      Spec.Xts.block (ciphOf enc R w) (bytesAt m Q 16) (bytesAt m P 16) := by
  rw [st_xor, hres, Spec.Xts.block, AesCbc.bytesAt_toList m P, AesCbc.bytesAt_toList m Q, ← load_state m P,
    ← load_state m Q, ← st_xor]
  cases enc <;> simp only [ciphOf, result, Bool.not_false, Bool.not_true, ite_true, ite_false,
    Bool.false_eq_true, Spec.Cbc.aesWith, Spec.Cbc.aesInvWith, ofFn_toList]


theorem flip_xor (a b : BitVec 128) :
    Proof.Aes.PPC64LE.Crypto.flip (a ^^^ b) =
      Proof.Aes.PPC64LE.Crypto.flip a ^^^ Proof.Aes.PPC64LE.Crypto.flip b := by
  simp only [Proof.Aes.PPC64LE.Crypto.flip, Proof.Aes.PPC64LE.Crypto.swapDwords_xor, rev128_xor]

/-- Block `j` at `r6` XORed with slot `j`, in the rounds' byte order. -/
theorem readTweaked_ok (s₀ : State) {j : Nat} (hj : j < 8) (t : State) (r19 : t.gpr .r19 = S s₀)
    (h0 : t.gpr .r0 = 0) (hm : t.vpr mask = byteMask)
    (hb : InRegions (t.rd ++ t.wr) (t.gpr .r6) 16) (hs : InRegions (t.rd ++ t.wr) (sl s₀ j) 16) :
    WP isa (.block (readTweaked j)) t fun u =>
      u.vpr (breg j) = rev128 (t.mem.read (t.gpr .r6) 16) ^^^ rev128 (t.mem.read (sl s₀ j) 16) ∧
      u.gpr .r6 = t.gpr .r6 + 16 ∧ Local [.r6, .r7] [.v9, breg j] t u := by
  have hv9 := breg_v9 hj
  have hmk := breg_mask hj
  have hb0 : InRegions (t.rd ++ t.wr) (t.gpr .r6 + t.gpr .r0) 16 := by
    rw [h0]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hb
  rw [readTweaked]
  refine WP.cons (exec_lxvd2x (breg j) .r6 .r0 t (by decide) hb0) ?_
  refine WP.cons (exec_addi' (d := .r7) (n := .r19) (imm := slot j) (by simp only [slot]; omega)) ?_
  refine WP.cons (exec_lxvd2x .v9 .r7 .r0 _ (by decide) ?_) ?_
  · simp only [RegUpd.rd_write, RegUpd.wr_write, rd_writeV, wr_writeV, RegUpd.gpr_write_self, RegUpd.gpr_write,
      gpr_writeV, ite_eq_right (show Reg.r0 ≠ .r7 by decide), r19, h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    exact hs
  refine WP.cons (show exec (.vop (.logic .xor (breg j) (breg j) .v9)) _ = some _ from rfl) ?_
  refine WP.cons (exec_flip (breg j) (breg j) _ ?_) ?_
  · simp only [vpr_writeV, vpr_write, ite_eq_right hmk.symm, ite_eq_right (show mask ≠ .v9 by decide)]
    exact hm
  refine WP.cons (exec_addi' (d := .r6) (n := .r6) (imm := 16) (by decide)) (wp_nil ?_)
  refine ⟨?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun r hr => ?_, ?_⟩⟩
  · simp only [vpr_write, vpr_writeV, ite_true, ite_eq_right hv9, ite_eq_right hv9.symm, RegUpd.gpr_write_self,
      RegUpd.gpr_write, gpr_writeV, ite_eq_right (show Reg.r0 ≠ .r7 by decide), r19, h0, mem_writeV,
      RegUpd.mem_write, BitVec.ofNat_eq_ofNat, BitVec.add_zero, flip_xor, Proof.Aes.PPC64LE.Crypto.flip_load]
  · simp only [RegUpd.gpr_write_self, RegUpd.gpr_write, gpr_writeV, ite_eq_right (show Reg.r6 ≠ .r7 by decide)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, gpr_writeV, ite_eq_right hr.1, ite_eq_right hr.2]
  · simp only [RegUpd.rd_write, rd_writeV]
  · simp only [RegUpd.wr_write, wr_writeV]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_write, vpr_writeV, ite_eq_right hr.1, ite_eq_right hr.2]
  · simp only [RegUpd.mem_write, mem_writeV]

/-- Blocks `0` to `c - 1` read at `r6` and XORed with their slots. -/
structure RInv (s₀ t : State) (D : Addr) (c : Nat) (u : State) : Prop where
  loc : Local [.r6, .r7] (.v9 :: batchRegs 8) t u
  r6 : u.gpr .r6 = D + BitVec.ofNat 64 (16 * c)
  val : ∀ i < c, u.vpr (breg i) =
    rev128 (t.mem.read (D + BitVec.ofNat 64 (16 * i)) 16) ^^^ rev128 (t.mem.read (sl s₀ i) 16)

theorem readsTweaked_ok (s₀ : State) (t : State) {D : Addr} (r6 : t.gpr .r6 = D) (r19 : t.gpr .r19 = S s₀)
    (h0 : t.gpr .r0 = 0) (hm : t.vpr mask = byteMask)
    (hb : ∀ j < 8, InRegions (t.rd ++ t.wr) (D + BitVec.ofNat 64 (16 * j)) 16)
    (hs : ∀ j < 8, InRegions (t.rd ++ t.wr) (sl s₀ j) 16) :
    WP isa (.block ((List.range 8).flatMap readTweaked)) t (RInv s₀ t D 8) := by
  refine wp_range_flatMap (M := isa) (RInv s₀ t D) (fun c u hc hu => ?_) 8 (Nat.le_refl _) t
    ⟨Local.refl _ _ _, by rw [r6, Nat.mul_zero]; exact (BitVec.add_zero D).symm, fun i hi => absurd hi (by omega)⟩
  have hl := hu.loc
  refine WP.mono (readTweaked_ok s₀ hc u (by rw [hl.keep.gpr (by decide), r19])
    (by rw [hl.keep.gpr (by decide), h0]) (by rw [hl.v _ (by simp [(batchFacts ⟨8, by decide⟩).2.2.1]), hm])
    (by rw [hl.keep.2.1, hl.keep.2.2, hu.r6]; exact hb c hc)
    (by rw [hl.keep.2.1, hl.keep.2.2]; exact hs c hc)) fun w ⟨hw, hp6, hw'⟩ => ⟨?_, ?_, fun i hi => ?_⟩
  · refine (hl.trans hw').weaken (by simp) fun a ha => ?_
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with (h | h) | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inr (h ▸ breg_mem hc)
  · rw [hp6, hu.r6]
    change D + BitVec.ofNat 64 (16 * c) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
  · by_cases hic : i = c
    · subst hic
      rw [hw, hu.r6, hl.mem]
    · rw [hw'.v _ (by simp [breg_v9 (show i < 8 by omega), breg_ne (show i < 8 by omega) hc hic]),
        hu.val i (by omega)]

/-- After the code before the rounds: the tweaks in their slots and XORed
into the eight blocks in `v0` … `v7`, and the registers of the rounds. -/
structure Front (enc : Bool) (s₀ : State) (k : Nat) (s u : State) : Prop where
  g : ∀ r ∈ preserved, u.gpr r = s.gpr r
  r6 : u.gpr .r6 = blk s₀ k
  r3 : u.gpr .r3 = W s₀
  inp : Inputs (R s₀) u
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  frame : Frame [ivR s₀, ⟨S s₀, 144⟩] s.mem u.mem
  slot : ∀ j < 8, bytesAt u.mem (sl s₀ j) 16 = chainK (AesXts.xtsMode enc) s₀ (k + j)
  iv : bytesAt u.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ (k + 8)
  val : ∀ j < 8, u.vpr (breg j) =
    rev128 (u.mem.read (blk s₀ (k + j)) 16) ^^^ rev128 (u.mem.read (sl s₀ j) 16)

theorem front_wp (enc : Bool) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (h : LInv (AesXts.xtsMode enc) s₀ k s) :
    WP isa (.block (tweaks8 ++ vsetup ++ (List.range 8).flatMap readTweaked ++
      ([.subi .r6 .r6 128] : List Instr))) s (Front enc s₀ k s) := by
  have hR := h.regs hp
  simp only [List.append_assoc]
  refine tweaks8_wp enc hp hk h fun t ht => ?_
  have gt (r : Reg) (hr : r ∈ preserved) : t.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h9, h10, h11, h12⟩ := pres_ne hr
    exact ht.g r h9 h10 h11 h12
  have rwt : t.rd ++ t.wr = s.rd ++ s.wr := by rw [ht.rd, ht.wr]
  refine vsetup_wp hp (by rw [gt _ (by decide), h.r14]) (by rw [gt _ (by decide), h.r15])
    (by rw [gt _ (by decide), h.r17]) (by rw [rwt, hR]) fun u hu => ?_
  have h0 := hu.inp.zero
  have hm := hu.inp.mask
  rw [WP.block_append_iff]
  refine WP.mono (readsTweaked_ok s₀ u hu.r6 (by rw [hu.g _ (by decide), gt _ (by decide), h.r19]) h0 hm
    (fun j hj => by rw [hu.rd, hu.wr, rwt, hR, blk_add]; exact in_rw (by simp) (cBlk16 hp (by omega)))
    fun j hj => by rw [hu.rd, hu.wr, rwt, hR]; exact in_rw (by simp) (cSl16 s₀ hj)) fun x hx => ?_
  refine WP.cons (exec_subi' (d := .r6) (n := .r6) (imm := 128) (by decide)) (wp_nil ?_)
  have mx : x.mem = t.mem := by rw [hx.loc.mem, hu.mem]
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · obtain ⟨-, -, -, h6, h7, -⟩ := pres_ne hr
    rw [RegUpd.gpr_write, ite_eq_right h6, hx.loc.keep.gpr (by simp [h6, h7]), hu.g r hr, gt r hr]
  · rw [RegUpd.gpr_write_self, hx.r6, show BitVec.ofNat 64 (16 * 8) = BitVec.ofNat 64 128 from rfl]
    exact BitVec.add_sub_cancel _ _
  · rw [RegUpd.gpr_write, ite_eq_right (by decide), hx.loc.keep.gpr (by decide), hu.r3]
  · refine inputs_of_local hu.inp (hx.loc.trans (Local.write x .r6 _)) (by decide) (by decide) (by decide)
      (by simp [(batchFacts ⟨8, by decide⟩).2.2.1])
  · rw [RegUpd.rd_write, hx.loc.keep.2.1, hu.rd, ht.rd]
  · rw [RegUpd.wr_write, hx.loc.keep.2.2, hu.wr, ht.wr]
  · rw [RegUpd.mem_write, mx]; exact ht.frame
  · rw [RegUpd.mem_write, mx]; exact ht.slot
  · rw [RegUpd.mem_write, mx]; exact ht.iv
  · rw [vpr_write, hx.val j hj, RegUpd.mem_write, mx, hu.mem, blk_add]

/-- Block `j` put back in memory's byte order, XORed with slot `j` and stored at `r6`. -/
theorem writeTweaked_ok (s₀ : State) {j : Nat} (hj : j < 8) (t : State) (r19 : t.gpr .r19 = S s₀)
    (h0 : t.gpr .r0 = 0) (hm : t.vpr mask = byteMask)
    (hs : InRegions (t.rd ++ t.wr) (sl s₀ j) 16) (hw : InRegions t.wr (t.gpr .r6) 16) :
    WP isa (.block (writeTweaked j)) t fun u =>
      u.mem = t.mem.write (t.gpr .r6) 16
        (rev128 (t.vpr (breg j) ^^^ rev128 (t.mem.read (sl s₀ j) 16))) ∧
      u.gpr .r6 = t.gpr .r6 + 16 ∧ Keep [.r6, .r7] t u ∧ (∀ r, r ∉ [breg j, .v9] → u.vpr r = t.vpr r) := by
  have hv9 := breg_v9 hj
  have hmk := breg_mask hj
  rw [writeTweaked]
  refine WP.cons (exec_flip (breg j) (breg j) t hm) ?_
  refine WP.cons (exec_addi' (d := .r7) (n := .r19) (imm := slot j) (by simp only [slot]; omega)) ?_
  refine WP.cons (exec_lxvd2x .v9 .r7 .r0 _ (by decide) ?_) ?_
  · simp only [RegUpd.rd_write, RegUpd.wr_write, rd_writeV, wr_writeV, RegUpd.gpr_write_self, RegUpd.gpr_write,
      gpr_writeV, ite_eq_right (show Reg.r0 ≠ .r7 by decide), r19, h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    exact hs
  refine WP.cons (show exec (.vop (.logic .xor (breg j) (breg j) .v9)) _ = some _ from rfl) ?_
  refine WP.cons (exec_stxvd2x (breg j) .r6 .r0 _ (by decide) ?_) ?_
  · simp only [wr_writeV, gpr_writeV, RegUpd.wr_write, RegUpd.gpr_write, ite_eq_right (show Reg.r6 ≠ .r7 by decide),
      ite_eq_right (show Reg.r0 ≠ .r7 by decide), h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    exact hw
  refine WP.cons (exec_addi' (d := .r6) (n := .r6) (imm := 16) (by decide)) (wp_nil ?_)
  refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, fun r hr => ?_⟩
  · simp only [RegUpd.mem_write, mem_writeV, vpr_writeV, vpr_write, ite_true, ite_eq_right hv9, ite_eq_right hv9.symm,
      gpr_writeV, RegUpd.gpr_write, ite_eq_right (show Reg.r6 ≠ .r7 by decide),
      ite_eq_right (show Reg.r0 ≠ .r7 by decide), h0, r19, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [Proof.Aes.PPC64LE.Crypto.swapDwords_xor, Proof.Aes.PPC64LE.Crypto.flip_store, swapDwords_involutive,
      rev128_xor, rev128_rev128]
  · simp only [RegUpd.gpr_write_self, RegUpd.gpr_write, gpr_writeV, ite_eq_right (show Reg.r6 ≠ .r7 by decide)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, gpr_writeV, ite_eq_right hr.1, ite_eq_right hr.2]
  · simp only [RegUpd.rd_write, rd_writeV]
  · simp only [RegUpd.wr_write, wr_writeV]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_write, vpr_writeV, ite_eq_right hr.1, ite_eq_right hr.2]

/-- The stores of `c` of the eight blocks, each XORed with its slot, in place at `D`. -/
structure WInv (s₀ t : State) (D : Addr) (c : Nat) (u : State) : Prop where
  keep : Keep [.r6, .r7] t u
  ptr : u.gpr .r6 = D + BitVec.ofNat 64 (16 * c)
  processed : Proof.Aes.Memory.Processed t.mem u.mem D 8 c
    fun i => aesState (t.vpr (breg i) ^^^ rev128 (t.mem.read (sl s₀ i) 16))
  frame : Frame [⟨D, 128⟩] t.mem u.mem
  val : ∀ i, c ≤ i → i < 8 → u.vpr (breg i) = t.vpr (breg i)
  mask : u.vpr mask = t.vpr mask

theorem writesTweaked_ok (s₀ : State) (t : State) {D : Addr} (r6 : t.gpr .r6 = D) (r19 : t.gpr .r19 = S s₀)
    (h0 : t.gpr .r0 = 0) (hm : t.vpr mask = byteMask)
    (hs : ∀ j < 8, InRegions (t.rd ++ t.wr) (sl s₀ j) 16)
    (hd : ∀ j < 8, (⟨sl s₀ j, 16⟩ : Region).Disjoint ⟨D, 128⟩)
    (hw : ∀ j < 8, InRegions t.wr (D + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block ((List.range 8).flatMap writeTweaked)) t (WInv s₀ t D 8) := by
  refine wp_range_flatMap (M := isa) (WInv s₀ t D) (fun c u hc hu => ?_) 8 (Nat.le_refl _) t
    ⟨Keep.refl _ _, by rw [r6, Nat.mul_zero]; exact (BitVec.add_zero D).symm,
      Proof.Aes.Memory.Processed.refl _ _ _ _, Frame.refl _ _, fun _ _ _ => rfl, rfl⟩
  have hsl : u.mem.read (sl s₀ c) 16 = t.mem.read (sl s₀ c) 16 :=
    hu.frame.read (Region.contains_self _ _) (one_disj (hd c hc)) (by decide)
  refine WP.mono (writeTweaked_ok s₀ hc u (by rw [hu.keep.gpr (by decide), r19])
    (by rw [hu.keep.gpr (by decide), h0]) (hu.mask.trans hm)
    (by rw [hu.keep.2.1, hu.keep.2.2]; exact hs c hc)
    (by rw [hu.ptr, hu.keep.2.2]; exact hw c hc)) fun w ⟨hwm, hw6, hwk, hwv⟩ => ?_
  have hp := hu.processed.store
    (v := rev128 (u.vpr (breg c) ^^^ rev128 (u.mem.read (sl s₀ c) 16))) (by decide) hc (by
    intro j hj
    change VG.VectorCrypto.vbyte (rev128 (u.vpr (breg c) ^^^ rev128 (u.mem.read (sl s₀ c) 16))) j = _
    rw [← VG.Proof.Aes.Vector.getD_st _ hj, hu.val c (Nat.le_refl _) hc, hsl]
    rfl)
  refine ⟨hu.keep.trans hwk |>.mono (by simp), ?_, ?_, ?_, fun i hi hi8 => ?_, ?_⟩
  · rw [hw6, hu.ptr]
    change D + BitVec.ofNat 64 (16 * c) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
  · rw [hwm, hu.ptr]; exact hp.1
  · rw [hwm, hu.ptr]; exact hu.frame.trans hp.2
  · rw [hwv _ (by simp [breg_ne hi8 hc (by omega), breg_v9 hi8]), hu.val i (by omega) hi8]
  · rw [hwv _ (by simp [(breg_mask hc).symm, show mask ≠ .v9 by decide]), hu.mask]

theorem back_wp (enc : Bool) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s u v : State}
    (h : LInv (AesXts.xtsMode enc) s₀ k s) (hu : Front enc s₀ k s u)
    (hv : ∀ b ∈ batchRegs 8, aesState (v.vpr b) =
      result (!enc) (R s₀) (schedule (R s₀) u) (aesState (u.vpr b)))
    (hl : Local [.r9, .r10] (key :: batchRegs 8) u v) :
    WP isa (.block ((List.range 8).flatMap writeTweaked ++ advance8)) v
      (LInv (AesXts.xtsMode enc) s₀ (k + 8)) := by
  have hR := h.regs hp
  have hW := h.wrs hp
  have facts := batchFacts ⟨8, by decide⟩
  have gv (r : Reg) (hr : r ∈ preserved) : v.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h9, h10, -⟩ := pres_ne hr
    rw [hl.keep.gpr (by simp [h9, h10]), hu.g r hr]
  have h0 : v.gpr .r0 = 0 := (hl.keep.gpr (by decide)).trans hu.inp.zero
  have hm : v.vpr mask = byteMask := (hl.v _ (by simp [facts.2.2.1])).trans hu.inp.mask
  have rwv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [hl.keep.2.1, hl.keep.2.2, hu.rd, hu.wr]
  have r6v : v.gpr .r6 = blk s₀ k := by rw [hl.keep.gpr (by decide), hu.r6]
  rw [WP.block_append_iff]
  refine WP.mono (writesTweaked_ok s₀ v r6v (by rw [gv _ (by decide), h.r19]) h0 hm
    (fun j hj => by rw [rwv, hR]; exact in_rw (by simp) (cSl16 s₀ hj))
    (fun j hj => by simpa using (hp.dSB (j := j) (m := 8) (by omega) hk))
    fun j hj => ?_) fun y hy => ?_
  · rw [hl.keep.2.2, hu.wr, hW, blk_add]
    exact in_rw (by simp) (cBlk16 hp (by omega))
  have gy (r : Reg) (hr : r ∈ preserved) : y.gpr r = s.gpr r := by
    obtain ⟨-, -, -, h6, h7, -⟩ := pres_ne hr
    rw [hy.keep.gpr (by simp [h6, h7]), gv r hr]
  refine advance8_regs hk (by rw [gy _ (by decide), h.r17]) (by rw [gy _ (by decide), h.r18])
    fun z r17 r18 keep mz rdz wrz => ?_
  have gz (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : z.gpr r = s.gpr r := by
    rw [keep r h17 h18, gy r hr]
  have mu : v.mem = u.mem := hl.mem
  have big : Frame (Big s₀) s₀.mem u.mem :=
    (UPre.big_of h.frame).trans (hu.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  have hw : schedule (R s₀) u = wK s₀ := by
    rw [Proof.Aes.PPC64LE.Crypto.schedule, hu.r3, UPre.sched_bytes hp big]
  refine group_step (xts_steps enc) hp hk h ?_ ?_ ?_ r17 r18 ?_ (fun r hr hv => ?_) ?_ ?_ ?_
    (fun j hj => ?_) ?_
  · rw [gz .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [gz .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [gz .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [gz .r19 (by decide) (by decide) (by decide), h.r19]
  · exact gz r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e]))
  · rw [rdz, hy.keep.2.1, hl.keep.2.1, hu.rd]
  · rw [wrz, hy.keep.2.2, hl.keep.2.2, hu.wr]
  · rw [mz]
    refine (hu.frame.sub fun r hr => ?_).trans (mu ▸ hy.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, slR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · have hi : k + j < N s₀ := by omega
    have hst := hy.processed.stateAt (j := j) hj (Nat.le_refl _)
    rw [mz, ← blk_add, AesCbc.bytesAt_toList, hst, mu,
      xts_vec enc (R s₀) (wK s₀) u.mem (blk s₀ (k + j)) (sl s₀ j) (v.vpr (breg j))
        (by rw [hv _ (breg_mem hj), hu.val j hj, hw]),
      hu.slot j hj, bytesAt_frame hu.frame (fun r hr => ?_) (by decide), h.blockAt (by omega) hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.blk_iv hi
    · exact hp.dBG hi
  · rw [mz, bytesAt_frame hy.frame (one_disj (hp.dIB hk)) (by decide), mu, hu.iv]

theorem vgroup_ok (enc : Bool) : GroupOk (AesXts.xtsMode enc) (vgroup (!enc)) := by
  intro s₀ hp k hk s h
  have facts := batchFacts ⟨8, by decide⟩
  rw [vgroup]
  refine WP.seq (WP.mono (front_wp enc hp hk h) fun u hu => ?_)
  exact WP.seq (WP.mono (Proof.Aes.PPC64LE.Crypto.aes_ok (!enc) (batchRegs 8) facts.1 facts.2.1 facts.2.2.1
    hu.inp) fun v ⟨hv, hl⟩ => back_wp enc hp hk h hu hv hl)

end Vec

theorem vgroup_ct (inverse : Bool) {M : AesCbc.Mode}
    (ht : ∃ h, (vectorTaint.check (Taint.ofRegs vars) (vgroup inverse) h).isSome = true) :
    GroupCt M (vgroup inverse) := by
  intro s₀ s₀' _ _ hq k
  obtain ⟨_, ht⟩ := ht
  exact RelCT.taint (A := vectorTaint) (Taint.ofRegs vars)
    (fun _ _ h => ⟨by rw [h.2.1.2, h.2.2.2, pub_sp hq],
      fun r h' => LInv.agree hq h.2.1.1 h.2.2.1 r (Taint.mem_ofRegs.mp h')⟩) ht

theorem encGroup_taint :
    ∃ h, (vectorTaint.check (Taint.ofRegs vars) (vgroup false) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroup_taint :
    ∃ h, (vectorTaint.check (Taint.ofRegs vars) (vgroup true) h).isSome = true := ⟨_, by taint_decide⟩

theorem encGroup_ok : GroupOk (AesXts.xtsMode true) (vgroup false) := vgroup_ok true

theorem decGroup_ok : GroupOk (AesXts.xtsMode false) (vgroup true) := vgroup_ok false

theorem encGroup_ct : GroupCt (AesXts.xtsMode true) (vgroup false) :=
  vgroup_ct false encGroup_taint

theorem decGroup_ct : GroupCt (AesXts.xtsMode false) (vgroup true) :=
  vgroup_ct true decGroup_taint

theorem encrypt_correct (s : State) (hs : (modePPC64LE (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := batched_wp encGroup_ok encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (modePPC64LE (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := batched_wp decGroup_ok decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode true)).pre
    (modePPC64LE (AesXts.xtsMode true)).pub encrypt :=
  batched_ct encGroup_ok encGroup_ct encBody_ok encBody_ct

theorem decrypt_ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode false)).pre
    (modePPC64LE (AesXts.xtsMode false)).pub decrypt :=
  batched_ct decGroup_ok decGroup_ct decBody_ok decBody_ct

theorem encrypt_noFrames : encrypt.noFrames = true := by decide +kernel

theorem decrypt_noFrames : decrypt.noFrames = true := by decide +kernel

end VG.Proof.AesXts.PPC64LE
