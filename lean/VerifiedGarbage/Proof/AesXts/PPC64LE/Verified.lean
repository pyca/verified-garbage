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
public import VerifiedGarbage.Proof.AesXts.PPC64LE.Rounds
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Vec
import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
import VerifiedGarbage.Proof.AesXts.Alpha
meta import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
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
meta import VerifiedGarbage.Proof.AesXts.PPC64LE.Rounds
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups

/-!
# XTS-AES on PPC64LE: the contracts

`Verified` for `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`: AES-CBC's
`batched_wp` and `batched_ct` (`Proof/AesCbc/PPC64LE/`) with the bodies of
`Body.lean` and the groups of eight blocks proven here (`vgroup_ok`: the
tweaks doubled in two words and saved in the slots, then the blocks in
vector registers through `Proof/Aes/PPC64LE/Crypto/`'s rounds), and the
contracts of `Spec/Xts/Contract.lean` from `modePPC64LE (xtsMode enc)`.

The groups keep round keys 1–9 in `kreg 1` … `kreg 9` (`KeysIn`), which
`preload` loads once before the first group (`preload_ok`): AES-CBC's
`batchedX_wp` and `batchedX_ct` carry them from group to group, and the
rounds with them are `Rounds.lean`'s `aesRes_ok`.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LE
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.PPC64LE
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes copyMem copyMem_frame copyMem_bytes aesWith_state
  aesInvWith_state)
open VG.Impl.AesCbc.PPC64LE (slot advance8 vsetup xorSlots)
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
  have hlt : ((blks s₀).take i).length = i := by simp [Spec.Cbc.blocksAt]; omega_using [hi]
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

/-! ## Steps that leave the vector registers as they were -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wpV_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _) rfl)

theorem wpV_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _) rfl)

theorem wpV_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _) rfl)

theorem wpV_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _) rfl)

theorem wpV_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _) rfl)

theorem wpV_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (Upd.write _ _ _) rfl)

theorem wpV_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl d n sh :: is)) s Q :=
  WP.cons (exec_lsl h) (k _ (Upd.write _ _ _) rfl)

theorem wpV_addi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _) rfl)

theorem wpV_subi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  WP.cons (exec_subi hn h) (k _ (Upd.write _ _ _) rfl)

theorem wpV_ld {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _) rfl)
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

theorem wpV_std {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → s'.vpr = s.vpr → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

end

/-- `dbl`: the tweak in `r9` and `r10` times `α`. -/
theorem dbl_wp {s : State} {rest : List Instr} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r9 = aLo (s.gpr .r9) (s.gpr .r10) → s'.gpr .r10 = aHi (s.gpr .r9) (s.gpr .r10) →
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.vpr = s.vpr → WP isa (.block rest) s' Φ) :
    WP isa (.block (dbl ++ rest)) s Φ := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wpV_lsr (by decide) fun s₃ u₃ v₃ => wpV_li (by decide) fun s₄ u₄ v₄ => wpV_sub fun s₅ u₅ v₅ => ?_
  refine wpV_li (by decide) fun s₆ u₆ v₆ => wpV_and fun s₇ u₇ v₇ => ?_
  refine wpV_lsr (by decide) fun s₈ u₈ v₈ => wpV_lsl (by decide) fun s₉ u₉ v₉ => wpV_xor fun s₁₀ u₁₀ v₁₀ => ?_
  refine wpV_lsl (by decide) fun s₁₁ u₁₁ v₁₁ => wpV_or fun s₁₂ u₁₂ v₁₂ => ?_
  refine k s₁₂ ?_ ?_ (fun r h9 h10 h11 h12 => ?_) ?_ ?_ ?_ ?_
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
  · rw [v₁₂, v₁₁, v₁₀, v₉, v₈, v₇, v₆, v₅, v₄, v₃]

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
  v : t.vpr = s.vpr

theorem tweakRegs_wp (enc : Bool) {s₀ : State} {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (hW₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀]) (hS : s.gpr .r19 = S s₀)
    (h0 : wb (s.gpr .r9) (s.gpr .r10) = chainK (AesXts.xtsMode enc) s₀ k)
    (m : Nat) (hm : m ≤ 8) {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ t, TJ enc s₀ k m s t → WP isa (.block rest) t Φ) :
    WP isa (.block ((List.range m).flatMap tweakReg ++ rest)) s Φ := by
  induction m generalizing rest Φ with
  | zero =>
    exact cont s ⟨fun _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _),
      by simpa using h0, rfl⟩
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]
    refine ih (by omega_using [hm]) fun t ht => ?_
    have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [ht.wr, hW₀]
    have r19 : t.gpr .r19 = S s₀ := by rw [ht.g _ (by decide) (by decide) (by decide) (by decide), hS]
    simp only [tweakReg, List.cons_append, List.nil_append]
    refine wpV_std (a := sl s₀ m) (by decide) ⟨by simp only [slot]; omega_using [hm], by simp only [slot]; omega_using []⟩
      (by rw [r19]) (by rw [hW]; exact in_rw (by simp) (cSl s₀ (by omega_using [hm]))) fun t₁ u₁ v₁ => ?_
    refine wpV_std (a := sl s₀ m + BitVec.ofNat 64 8) (by decide)
      ⟨by simp only [slot]; omega_using [hm], by simp only [slot]; omega_using []⟩
      (by rw [u₁.gpr, r19, sl8]) (by rw [u₁.wr, hW]; exact in_rw (by simp) (cSl8 s₀ (by omega_using [hm])))
      fun t₂ u₂ v₂ => ?_
    have hm₂ : t₂.mem = (t.mem.writeW (sl s₀ m) (t.gpr .r9)).writeW (sl s₀ m + BitVec.ofNat 64 8)
        (t.gpr .r10) := by rw [u₂.mem, u₁.mem, u₁.gpr]
    refine dbl_wp fun t₃ g9 g10 g₃ mem₃ rd₃ wr₃ v₃ => cont t₃ ?_
    refine ⟨fun r h9 h10 h11 h12 => ?_, by rw [rd₃, u₂.rd, u₁.rd, ht.rd], by rw [wr₃, u₂.wr, u₁.wr, ht.wr],
      ?_, fun j hj => ?_, ?_, by rw [v₃, v₂, v₁, ht.v]⟩
    · rw [g₃ r h9 h10 h11 h12, u₂.gpr, u₁.gpr, ht.g r h9 h10 h11 h12]
    · rw [mem₃, hm₂]
      exact ht.frame.trans ((pair_frame _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sl_sub s₀ (by omega_using [hm])⟩)
    · rw [mem₃, hm₂]
      by_cases hjm : j < m
      · rw [bytesAt_frame (pair_frame _ _ _ _) (one_disj (dSS s₀ (by omega_using [hm, hj]) (by omega_using [hm]) (by omega_using [hjm])))
          (by decide), ht.slot j hjm]
      · have : j = m := by omega_using [hj, hjm]
        subst this
        rw [bytes_pair, ht.w]
    · rw [g9, g10, u₂.gpr, u₁.gpr, wb_alpha, ht.w, ← Nat.add_assoc, xts_chain enc s₀ (by omega_using [hk, hm])]

/-- The tweaks of the eight blocks of a group in slots 0–7, and the next one
at `Iv`. -/
structure TW (enc : Bool) (s₀ : State) (k : Nat) (s t : State) : Prop where
  g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [ivR s₀, ⟨S s₀, 144⟩] s.mem t.mem
  slot : ∀ j < 8, bytesAt t.mem (sl s₀ j) 16 = chainK (AesXts.xtsMode enc) s₀ (k + j)
  iv : bytesAt t.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ (k + 8)
  v : t.vpr = s.vpr

theorem tweaks8_wp (enc : Bool) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (h : LInv (AesXts.xtsMode enc) s₀ k s) {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ t, TW enc s₀ k s t → WP isa (.block rest) t Φ) :
    WP isa (.block (tweaks8 ++ rest)) s Φ := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := h.regs hp
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := h.wrs hp
  simp only [tweaks8, List.cons_append, List.nil_append, List.append_assoc]
  refine wpV_ld (a := Iv s₀) (by decide) (by decide) (by rw [h.r16, ofNat_zero_add])
    (by rw [hR]; exact in_rw (by simp) cIv0) fun t₁ u₁ v₁ => ?_
  refine wpV_ld (a := Iv s₀ + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₁.other _ (by decide), h.r16])
    (by rw [u₁.rd, u₁.wr, hR]; exact in_rw (by simp) cIv8) fun t₂ u₂ v₂ => ?_
  have w₂ : wb (t₂.gpr .r9) (t₂.gpr .r10) = chainK (AesXts.xtsMode enc) s₀ k := by
    rw [u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, ← bytes_read, h.iv]
  refine tweakRegs_wp enc hk (by rw [u₂.wr, u₁.wr, hW]) (by rw [u₂.other _ (by decide),
    u₁.other _ (by decide), h.r19]) w₂ 8 (by decide) fun t₃ ht => ?_
  have r16 : t₃.gpr .r16 = Iv s₀ := by
    rw [ht.g _ (by decide) (by decide) (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.r16]
  have hW₃ : t₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [ht.wr, u₂.wr, u₁.wr, hW]
  refine wpV_std (a := Iv s₀) (by decide) (by decide) (by rw [r16, ofNat_zero_add])
    (by rw [hW₃]; exact in_rw (by simp) cIv0) fun t₄ u₄ v₄ => ?_
  refine wpV_std (a := Iv s₀ + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₄.gpr, r16])
    (by rw [u₄.wr, hW₃]; exact in_rw (by simp) cIv8) fun t₅ u₅ v₅ => cont t₅ ?_
  have hm₅ : t₅.mem = (t₃.mem.writeW (Iv s₀) (t₃.gpr .r9)).writeW (Iv s₀ + BitVec.ofNat 64 8)
      (t₃.gpr .r10) := by rw [u₅.mem, u₄.mem, u₄.gpr]
  have hm₂ : t₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨fun r h9 h10 h11 h12 => ?_, by rw [u₅.rd, u₄.rd, ht.rd, u₂.rd, u₁.rd],
    by rw [u₅.wr, u₄.wr, ht.wr, u₂.wr, u₁.wr], ?_, fun j hj => ?_, ?_, by rw [v₅, v₄, ht.v, v₂, v₁]⟩
  · rw [u₅.gpr, u₄.gpr, ht.g r h9 h10 h11 h12, u₂.other _ h10, u₁.other _ h9]
  · rw [hm₅, ← hm₂]
    refine (ht.frame.sub fun r hr => ?_).trans ((pair_frame _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩
  · rw [hm₅, bytesAt_frame (pair_frame _ _ _ _) (one_disj (hp.dIS (by omega_using [hj])).symm) (by decide), ht.slot j hj]
  · rw [hm₅, bytes_pair, ht.w]

/-! ## The eight blocks in vector registers -/

section Vec
open VG.Proof.Aes.PPC64LE.Crypto (Local Inputs aesState result schedule BatchRead readValue Stored
  batchFacts breg_mem breg_ne load_state aesState_byte)
open VG.Impl.Aes.PPC64LE.Crypto (breg batchRegs key mask byteMask)
open VG.Proof.Aes.PPC64LE.Crypto (IsKey Local)

/-- Round keys 1–9 of the schedule in `kreg 1` … `kreg 9`, as `preload`
leaves them and the groups keep them. -/
def KeysIn (s₀ : State) (v : VReg → BitVec 128) : Prop :=
  ∀ i, 1 ≤ i → i ≤ 9 → IsKey (v (kreg i)) (Spec.Aes.roundKey (wK s₀) i)

/-- The registers of the round keys are none of the others the groups use. -/
theorem kreg_out (i : Nat) {l : List VReg}
    (hl : ∀ r ∈ l, r ∈ ([.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v19] : List VReg)) :
    kreg i ∉ l := fun h => by
  have h1 := kreg_mem i
  have h2 := hl _ h
  revert h1 h2
  generalize kreg i = r
  cases r <;> decide

theorem kreg_inj {i j : Nat} (hi : 1 ≤ i ∧ i ≤ 9) (hj : 1 ≤ j ∧ j ≤ 9) (h : kreg i = kreg j) : i = j := by
  have : ∀ i < 10, ∀ j < 10, 1 ≤ i → 1 ≤ j → kreg i = kreg j → i = j := by decide
  exact this i (by omega_using [hi]) j (by omega_using [hj]) hi.1 hj.1 h

/-- `advance8_regs`, which leaves the vector registers as they were. -/
theorem advance8_regsV {s₀ : State} {k : Nat} (hk : k + 8 ≤ N s₀) {s : State} {Φ : State → Prop}
    (h17 : s.gpr .r17 = blk s₀ k) (h18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k))
    (h : ∀ s', s'.gpr .r17 = blk s₀ (k + 8) → s'.gpr .r18 = BitVec.ofNat 64 (N s₀ - (k + 8)) →
      (∀ r, r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.vpr = s.vpr → Φ s') :
    WP isa (.block advance8) s Φ := by
  have hN : N s₀ < 2 ^ 64 := (s₀.gpr .r7).isLt
  unfold advance8
  refine wpV_addi (by decide) (by decide) fun s₁ u₁ v₁ => wpV_subi (by decide) (by decide) fun s₂ u₂ v₂ =>
    wp_nil ?_
  refine h s₂ ?_ ?_ (fun r h₁ h₂ => ?_) ?_ ?_ ?_ ?_
  · rw [u₂.other _ (by decide), u₁.gpr, h17, Offset.add_add_eq _ (c := 16 * (k + 8)) (by omega_using [])]
  · rw [u₂.gpr, u₁.other _ (by decide), h18, Offset.ofNat_sub_ofNat (by omega_using [hk])]; rfl
  · rw [u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [v₂, v₁]

/-- The invariant holds after code that writes only `r0`, `r9`, `r11`, `r12`
and vector registers. -/
theorem linv_ofLocal {M : AesCbc.Mode} {s₀ : State} {k : Nat} {s t : State} {vs : List VReg}
    (h : LInv M s₀ k s) (hl : Local [.r0, .r9, .r11, .r12] vs s t) : LInv M s₀ k t where
  r14 := (hl.keep.gpr (by decide)).trans h.r14
  r15 := (hl.keep.gpr (by decide)).trans h.r15
  r16 := (hl.keep.gpr (by decide)).trans h.r16
  r17 := (hl.keep.gpr (by decide)).trans h.r17
  r18 := (hl.keep.gpr (by decide)).trans h.r18
  r19 := (hl.keep.gpr (by decide)).trans h.r19
  keep r hr hv := by
    obtain ⟨h0, -, -, -, -, -, h9, -, h11, h12⟩ := pres_ne hr
    exact (hl.keep.gpr (by simp [h0, h9, h11, h12])).trans (h.keep r hr hv)
  rd := hl.keep.2.1.trans h.rd
  wr := hl.keep.2.2.trans h.wr
  frame := by rw [hl.mem]; exact h.frame
  data := by rw [hl.mem]; exact h.data
  iv := by rw [hl.mem]; exact h.iv

/-- After the mask and the first `c` round keys of `preload`. -/
structure PInv (s₀ s : State) (c : Nat) (u : State) : Prop where
  loc : Local [.r0, .r9, .r11, .r12] [.v0, .v1, .v19, .v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18] s u
  r0 : u.gpr .r0 = 0
  mask : u.vpr mask = byteMask
  keys : ∀ i, 1 ≤ i → i ≤ c → IsKey (u.vpr (kreg i)) (Spec.Aes.roundKey (wK s₀) i)

theorem preload_ok (M : AesCbc.Mode) : PreOk M KeysIn preload := by
  intro s₀ hp k s h
  have hR := h.regs hp
  have hw : bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp (UPre.big_of h.frame)
  have hR₀ := hp.rounds
  rw [preload, WP.block_append_iff]
  refine WP.mono (Proof.Aes.PPC64LE.Crypto.setup_ok s) fun t ⟨h0, hm, _, hl⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (PInv s₀ s) (fun c u hc hu => ?_) 9 (Nat.le_refl _) t
    ⟨hl.weaken (by simp) (by simp), h0, hm, fun i h1 h2 => absurd h2 (by omega_using [h1])⟩) fun u hu =>
      ⟨linv_ofLocal h hu.loc, hu.keys⟩
  refine wpV_addi (by decide) (by omega_using [hc]) fun u₁ up₁ uv₁ => ?_
  have l₁ : Local [.r9] [] u u₁ :=
    ⟨⟨fun r hr => up₁.other r (by simpa using hr), up₁.rd, up₁.wr⟩, fun r _ => congrFun uv₁ r, up₁.mem⟩
  have r9 : u₁.gpr .r9 = W s₀ + BitVec.ofNat 64 (16 * (c + 1)) := by
    rw [up₁.gpr, hu.loc.keep.gpr (by decide), h.r14]
  refine WP.mono (Proof.Aes.PPC64LE.Crypto.load_ok (kreg (c + 1)) .r9 u₁ (by decide) (kreg_ne_mask _)
    ((l₁.keep.gpr (by decide)).trans hu.r0) ((l₁.v _ (by simp)).trans hu.mask) (by
      rw [l₁.keep.2.1, l₁.keep.2.2, hu.loc.keep.2.1, hu.loc.keep.2.2, hR, r9]
      have : c + 1 ≤ 14 := by omega_using [hc]
      exact in_rw (r := schR s₀) (by simp) (Offset.contains_base (d := 16 * (c + 1)) (n := 16) (k := 240) _
        (by omega_using [hc]) (by omega_using [hc])))) fun u₂ ⟨hv, ho⟩ => ?_
  have l₂ := Local.of_vector ho
  refine ⟨(hu.loc.trans (l₁.trans l₂)).weaken (by simp) fun r hr => ?_, (l₂.keep.gpr (by decide)).trans
    ((l₁.keep.gpr (by decide)).trans hu.r0), (l₂.v _ (by simpa using (kreg_ne_mask (c + 1)).symm)).trans
    ((l₁.v _ (by simp)).trans hu.mask), fun i h1 h2 => ?_⟩
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h
    · simpa using h
    · simp at h
    · subst h
      have := kreg_mem (c + 1)
      revert this
      generalize kreg (c + 1) = r
      cases r <;> decide
  · by_cases hi : i = c + 1
    · subst hi
      rw [hv, r9, l₁.mem, hu.loc.mem, ← hw]
      exact Proof.Aes.PPC64LE.Crypto.key_read s.mem (W s₀) (by rcases hR₀ with e | e | e <;> omega_using [hc, e])
    · rw [l₂.v _ (by simpa using fun e => hi (kreg_inj ⟨h1, by omega_using [hc, h2]⟩ ⟨by omega_using [], by omega_using [hc]⟩ e)),
        l₁.v _ (by simp)]
      exact hu.keys i h1 (by omega_using [h2, hi])

theorem preload_taint :
    ∃ h, (vectorTaint.check (Taint.ofRegs vars) (.block preload) h).isSome = true := ⟨_, by taint_decide⟩

theorem preload_ct (M : AesCbc.Mode) : PreCt M preload := fun {_} {_} _ _ hq _ => by
  obtain ⟨_, ht⟩ := preload_taint
  exact RelCT.taint (A := vectorTaint) (Taint.ofRegs vars)
    (fun _ _ h => ⟨by rw [h.1.2, h.2.2, pub_sp hq],
      fun r h' => LInv.agree hq h.1.1 h.2.1 r (Taint.mem_ofRegs.mp h')⟩) ht

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
  kv : ∀ i, u.vpr (kreg i) = s.vpr (kreg i)

theorem front_wp (enc : Bool) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (h : LInv (AesXts.xtsMode enc) s₀ k s) :
    WP isa (.block (tweaks8 ++ vsetup ++ (batchRegs 8).flatMap (Impl.Aes.PPC64LE.Crypto.readBlock false) ++
      ([.subi .r6 .r6 128] : List Instr) ++ xorSlots)) s (Front enc s₀ k s) := by
  have hR := h.regs hp
  simp only [List.append_assoc, List.singleton_append]
  refine tweaks8_wp enc hp hk h fun t ht => ?_
  have gt (r : Reg) (hr : r ∈ preserved) : t.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h9, h10, h11, h12⟩ := pres_ne hr
    exact ht.g r h9 h10 h11 h12
  have rwt : t.rd ++ t.wr = s.rd ++ s.wr := by rw [ht.rd, ht.wr]
  refine read8_wp hp hk (by rw [gt _ (by decide), h.r14]) (by rw [gt _ (by decide), h.r15])
    (by rw [gt _ (by decide), h.r17]) (by rw [rwt, hR]) fun u hu => ?_
  have h0 := hu.inp.zero
  have hm := hu.inp.mask
  refine WP.mono (xorSlots_ok s₀ u (by rw [hu.g _ (by decide), gt _ (by decide), h.r19]) h0 hm fun j hj => by
    rw [hu.rd, hu.wr, rwt, hR]; exact in_rw (by simp) (cSl16 s₀ hj)) fun x hx => ?_
  have mx : x.mem = t.mem := by rw [hx.loc.mem, hu.mem]
  refine ⟨fun r hr => ?_, by rw [hx.loc.keep.gpr (by decide), hu.r6], by rw [hx.loc.keep.gpr (by decide), hu.r3],
    inputs_of_local hu.inp hx.loc (by decide) (by decide) (by decide) (by simp [(batchFacts ⟨8, by decide⟩).2.2.1]),
    by rw [hx.loc.keep.2.1, hu.rd, ht.rd], by rw [hx.loc.keep.2.2, hu.wr, ht.wr],
    by rw [mx]; exact ht.frame, by rw [mx]; exact ht.slot, by rw [mx]; exact ht.iv, fun j hj => ?_,
    fun i => by rw [hx.loc.v _ (kreg_out i (by decide)), hu.vs _ (kreg_out i (by decide)), ht.v]⟩
  · obtain ⟨-, -, -, -, h7, -⟩ := pres_ne hr
    rw [hx.loc.keep.gpr (by simpa using h7), hu.g r hr, gt r hr]
  · rw [hx.val j hj, ite_eq_left hj, hu.val j hj, mx, hu.mem]

theorem back_wp (enc : Bool) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s u v : State}
    (h : LInv (AesXts.xtsMode enc) s₀ k s) (hu : Front enc s₀ k s u)
    (hv : ∀ b ∈ batchRegs 8, aesState (v.vpr b) =
      result (!enc) (R s₀) (schedule (R s₀) u) (aesState (u.vpr b)))
    (hl : Local [.r9, .r10, .r12] (key :: batchRegs 8) u v) (hx₀ : KeysIn s₀ v.vpr) :
    WP isa (.block (xorSlots ++ (batchRegs 8).flatMap (fun b => Impl.Aes.PPC64LE.Crypto.storeAdvance b) ++
      advance8)) v fun t => LInv (AesXts.xtsMode enc) s₀ (k + 8) t ∧ KeysIn s₀ t.vpr := by
  have hR := h.regs hp
  have hW := h.wrs hp
  have facts := batchFacts ⟨8, by decide⟩
  have gv (r : Reg) (hr : r ∈ preserved) : v.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, -, h9, h10, -, h12⟩ := pres_ne hr
    rw [hl.keep.gpr (by simp [h9, h10, h12]), hu.g r hr]
  have h0 : v.gpr .r0 = 0 := (hl.keep.gpr (by decide)).trans hu.inp.zero
  have hm : v.vpr mask = byteMask := (hl.v _ (by simp [facts.2.2.1])).trans hu.inp.mask
  have rwv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [hl.keep.2.1, hl.keep.2.2, hu.rd, hu.wr]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (xorSlots_ok s₀ v (by rw [gv _ (by decide), h.r19]) h0 hm fun j hj => by
    rw [rwv, hR]; exact in_rw (by simp) (cSl16 s₀ hj)) fun x hx => ?_
  have r6x : x.gpr .r6 = blk s₀ k := by
    rw [hx.loc.keep.gpr (by decide), hl.keep.gpr (by decide), hu.r6]
  refine WP.mono (stores_ok x r6x ((hx.loc.keep.gpr (by decide)).trans h0)
    ((hx.loc.v _ (by simp [facts.2.2.1])).trans hm) fun j hj => ?_) fun y hy => ?_
  · rw [hx.loc.keep.2.2, hl.keep.2.2, hu.wr, hW, blk_add]
    exact in_rw (by simp) (cBlk16 hp (by omega_using [hk, hj]))
  have gy (r : Reg) (hr : r ∈ preserved) : y.gpr r = s.gpr r := by
    obtain ⟨-, -, -, h6, h7, -⟩ := pres_ne hr
    rw [hy.keep.gpr (by simpa using h6), hx.loc.keep.gpr (by simpa using h7), gv r hr]
  refine advance8_regsV hk (by rw [gy _ (by decide), h.r17]) (by rw [gy _ (by decide), h.r18])
    fun z r17 r18 keep mz rdz wrz vz => ⟨?_, fun i h1 h9 => ?_⟩
  swap
  · rw [vz, hy.vs _ (kreg_out i (by decide)), hx.loc.v _ (kreg_out i (by decide))]
    exact hx₀ i h1 h9
  have gz (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : z.gpr r = s.gpr r := by
    rw [keep r h17 h18, gy r hr]
  have mu : x.mem = u.mem := by rw [hx.loc.mem, hl.mem]
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
  · rw [rdz, hy.keep.2.1, hx.loc.keep.2.1, hl.keep.2.1, hu.rd]
  · rw [wrz, hy.keep.2.2, hx.loc.keep.2.2, hl.keep.2.2, hu.wr]
  · rw [mz]
    refine (hu.frame.sub fun r hr => ?_).trans (mu ▸ hy.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, slR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · have hi : k + j < N s₀ := by omega_using [hk, hj]
    have hst := hy.processed.stateAt (j := j) hj (Nat.le_refl _)
    rw [mz, ← blk_add, AesCbc.bytesAt_toList, hst, hx.val j hj, ite_eq_left hj, hl.mem,
      xts_vec enc (R s₀) (wK s₀) u.mem (blk s₀ (k + j)) (sl s₀ j) (v.vpr (breg j))
        (by rw [hv _ (breg_mem hj), hu.val j hj, hw]),
      hu.slot j hj, bytesAt_frame hu.frame (fun r hr => ?_) (by decide), h.blockAt (by omega_using []) hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.blk_iv hi
    · exact hp.dBG hi
  · rw [mz, bytesAt_frame hy.frame (one_disj (hp.dIB hk)) (by decide), mu, hu.iv]

theorem vgroup_ok (enc : Bool) : GroupOkX (AesXts.xtsMode enc) KeysIn (vgroup (!enc)) := by
  intro s₀ hp k hk s h hx
  have facts := batchFacts ⟨8, by decide⟩
  rw [vgroup]
  refine WP.seq (WP.mono (front_wp enc hp hk h) fun u hu => ?_)
  have big : Frame (Big s₀) s₀.mem u.mem :=
    (UPre.big_of h.frame).trans (hu.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  have hw : schedule (R s₀) u = wK s₀ := by
    rw [Proof.Aes.PPC64LE.Crypto.schedule, hu.r3, UPre.sched_bytes hp big]
  have hkr (i : Nat) : kreg i ∉ batchRegs 8 := kreg_out i (by decide)
  exact WP.seq (WP.mono (aesRes_ok (!enc) (batchRegs 8) facts.1 facts.2.1 facts.2.2.1 hkr hu.inp hp.rounds
    fun i h1 h9 => by rw [hw, hu.kv]; exact hx i h1 h9) fun v ⟨hv, hl⟩ =>
      back_wp enc hp hk h hu hv hl fun i h1 h9 => by
        rw [hl.v _ (kreg_out i (by decide)), hu.kv]; exact hx i h1 h9)

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

theorem encGroup_ok : GroupOkX (AesXts.xtsMode true) KeysIn (vgroup false) := vgroup_ok true

theorem decGroup_ok : GroupOkX (AesXts.xtsMode false) KeysIn (vgroup true) := vgroup_ok false

theorem encGroup_ct : GroupCt (AesXts.xtsMode true) (vgroup false) :=
  vgroup_ct false encGroup_taint

theorem decGroup_ct : GroupCt (AesXts.xtsMode false) (vgroup true) :=
  vgroup_ct true decGroup_taint

theorem encrypt_correct (s : State) (hs : (modePPC64LE (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := batchedX_wp encGroup_ok (preload_ok _) encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (modePPC64LE (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := batchedX_wp decGroup_ok (preload_ok _) decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode true)).pre
    (modePPC64LE (AesXts.xtsMode true)).pub encrypt :=
  batchedX_ct encGroup_ok encGroup_ct (preload_ok _) (preload_ct _) encBody_ok encBody_ct

theorem decrypt_ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode false)).pre
    (modePPC64LE (AesXts.xtsMode false)).pub decrypt :=
  batchedX_ct decGroup_ok decGroup_ct (preload_ok _) (preload_ct _) decBody_ok decBody_ct

theorem encrypt_noFrames : encrypt.noFrames = true := by decide +kernel

theorem decrypt_noFrames : decrypt.noFrames = true := by decide +kernel

end VG.Proof.AesXts.PPC64LE
