module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Batch
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Value
public import VerifiedGarbage.Proof.Aes.Memory
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Batch
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Value
meta import VerifiedGarbage.Proof.Aes.Memory
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

-- separate module: XTS's groups, and CBC decryption's, share these proofs.
/-!
# AES on PPC64LE: eight blocks in vector registers

The pieces of a group of eight blocks that keeps the blocks in `v0` … `v7`
and runs them through `Impl.Aes.PPC64LE.Crypto.aes` together:

* `read8_wp`: the rounds' registers set up (`vsetup`) and the eight blocks
  at `r17` read.
* `xorSlots_ok`: slot `j` of the scratch buffer XORed into `breg j`.
* `stores_ok`: the eight registers stored in place, as `Processed` bytes.
* `st_xor`: the bytes of a XOR of vectors.
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE

open VG VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (slot xorSlot xorSlots vsetup)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.PPC64LE.Crypto (Local Inputs aesState BatchRead readValue Stored batchFacts breg_mem
  breg_ne aesState_byte)
open VG.Impl.Aes.PPC64LE.Crypto (breg batchRegs mask byteMask)

theorem breg_v9 {i : Nat} (hi : i < 8) : breg i ≠ .v9 := by
  have h : ∀ i : Fin 8, breg i ≠ .v9 := by decide
  exact h ⟨i, hi⟩

theorem breg_mask {i : Nat} (hi : i < 8) : breg i ≠ mask := by
  have h : ∀ i : Fin 8, breg i ≠ mask := by decide
  exact h ⟨i, hi⟩

/-- Slot `j` XORed into `breg j`. -/
theorem xorSlot_ok (s₀ : State) {j : Nat} (hj : j < 8) (t : State) (r19 : t.gpr .r19 = S s₀)
    (h0 : t.gpr .r0 = 0) (hm : t.vpr mask = byteMask) (hr : InRegions (t.rd ++ t.wr) (sl s₀ j) 16) :
    WP isa (.block (xorSlot j)) t fun u =>
      u.vpr (breg j) = t.vpr (breg j) ^^^ rev128 (t.mem.read (sl s₀ j) 16) ∧ Local [.r7] [.v9, breg j] t u := by
  rw [xorSlot, WP.block_append_iff]
  refine WP.cons (exec_addi' (d := .r7) (n := .r19) (imm := slot j) (by simp only [slot]; omega)) ?_
  have h7 : (t.write .r7 (t.gpr .r19 + BitVec.ofNat 64 (slot j))).gpr .r7 = sl s₀ j := by
    rw [RegUpd.gpr_write_self, r19]
  refine WP.mono (Proof.Aes.PPC64LE.Crypto.load_ok .v9 .r7 _ (by decide) (by decide)
    (by rw [RegUpd.gpr_write, ite_eq_right (by decide)]; exact h0) (by rw [vpr_write]; exact hm)
    (by rw [h7, RegUpd.rd_write, RegUpd.wr_write]; exact hr)) fun u ⟨hv, ho⟩ => ?_
  refine WP.mono (vector_step (.vop (.logic .xor (breg j) (breg j) .v9)) (breg j)
    (u.vpr (breg j) ^^^ u.vpr .v9) u rfl) fun w ⟨hw, hw'⟩ => ⟨?_, ?_⟩
  · rw [hw, hv, ho.v _ (by simpa only [List.mem_singleton] using breg_v9 hj), vpr_write, h7,
      RegUpd.mem_write]
  · exact (((Local.write t .r7 _).trans (Local.of_vector ho)).trans (Local.of_vector hw')).weaken
      (by simp) (by simp)

/-- The XOR of slots `0` to `c - 1` into `v0` … -/
structure XInv (s₀ t : State) (c : Nat) (u : State) : Prop where
  loc : Local [.r7] (.v9 :: batchRegs 8) t u
  val : ∀ i < 8, u.vpr (breg i) = if i < c then t.vpr (breg i) ^^^ rev128 (t.mem.read (sl s₀ i) 16)
    else t.vpr (breg i)

theorem xorSlots_ok (s₀ : State) (t : State) (r19 : t.gpr .r19 = S s₀)
    (h0 : t.gpr .r0 = 0) (hm : t.vpr mask = byteMask)
    (hr : ∀ j < 8, InRegions (t.rd ++ t.wr) (sl s₀ j) 16) :
    WP isa (.block xorSlots) t (XInv s₀ t 8) := by
  refine wp_range_flatMap (M := isa) (XInv s₀ t) (fun c u hc hu => ?_) 8 (Nat.le_refl _) t
    ⟨Local.refl _ _ _, fun i _ => by rw [ite_eq_right (Nat.not_lt_zero _)]⟩
  have hl := hu.loc
  refine WP.mono (xorSlot_ok s₀ hc u (by rw [hl.keep.gpr (by decide), r19])
    (by rw [hl.keep.gpr (by decide), h0]) (by rw [hl.v _ (by simp [(batchFacts ⟨8, by decide⟩).2.2.1]), hm])
    (by rw [hl.keep.2.1, hl.keep.2.2]; exact hr c hc)) fun w ⟨hw, hw'⟩ => ⟨?_, fun i hi => ?_⟩
  · refine (hl.trans hw').weaken (by simp) fun a ha => ?_
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with (h | h) | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inr (h ▸ breg_mem hc)
  · by_cases hic : i = c
    · subst hic
      rw [hw, hu.val i hi, ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _), hl.mem]
    · rw [hw'.v _ (by simp [breg_v9 hi, breg_ne hi hc hic]), hu.val i hi]
      by_cases hlt : i < c
      · rw [ite_eq_left hlt, ite_eq_left (by omega)]
      · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- The stores of `c` of the eight blocks, in place at `D`. -/
structure SInv (t : State) (D : Addr) (c : Nat) (u : State) : Prop where
  keep : Keep [.r6] t u
  ptr : u.gpr .r6 = D + BitVec.ofNat 64 (16 * c)
  processed : Proof.Aes.Memory.Processed t.mem u.mem D 8 c fun i => aesState (t.vpr (breg i))
  frame : Frame [⟨D, 128⟩] t.mem u.mem
  val : ∀ i, c ≤ i → i < 8 → u.vpr (breg i) = t.vpr (breg i)
  mask : u.vpr mask = t.vpr mask

theorem stores_ok (t : State) {D : Addr} (r6 : t.gpr .r6 = D) (h0 : t.gpr .r0 = 0)
    (hm : t.vpr mask = byteMask) (hw : ∀ j < 8, InRegions t.wr (D + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block ((batchRegs 8).flatMap fun v => Impl.Aes.PPC64LE.Crypto.storeAdvance v)) t
      (SInv t D 8) := by
  rw [batchRegs, List.flatMap_map]
  refine wp_range_flatMap (M := isa) (SInv t D) (fun c u hc hu => ?_) 8 (Nat.le_refl _) t
    ⟨Keep.refl _ _, by rw [r6, Nat.mul_zero]; exact (BitVec.add_zero D).symm,
      Proof.Aes.Memory.Processed.refl _ _ _ _, Frame.refl _ _, fun _ _ _ => rfl, rfl⟩
  have hz : u.gpr .r0 = 0 := (hu.keep.gpr (by decide)).trans h0
  have haddr : u.gpr .r6 + u.gpr .r0 = D + BitVec.ofNat 64 (16 * c) := by
    rw [hu.ptr, hz]; exact BitVec.add_zero _
  refine WP.mono (Proof.Aes.PPC64LE.Crypto.storeAdvance_ok (breg c) .r0 u (hu.mask.trans hm)
    (by rw [haddr, hu.keep.2.2]; exact hw c hc)) fun w hs => ?_
  have hp := hu.processed.store (v := rev128 (u.vpr (breg c))) (by decide) hc (by
    intro j hj
    change VG.VectorCrypto.vbyte (rev128 (u.vpr (breg c))) j = _
    rw [← VG.Proof.Aes.Vector.getD_st _ hj, hu.val c (Nat.le_refl _) hc]
    rfl)
  refine ⟨(hu.keep.trans hs.keep).mono (by simp), ?_, ?_, ?_, fun i hi hi8 => ?_, ?_⟩
  · rw [hs.ptr, hu.ptr]
    change D + BitVec.ofNat 64 (16 * c) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
  · rw [hs.mem, haddr]; exact hp.1
  · rw [hs.mem, haddr]; exact hu.frame.trans hp.2
  · rw [hs.v _ (by simp [breg_ne hi8 hc (by omega), breg_v9 hi8]), hu.val i (by omega) hi8]
  · rw [hs.v _ (by simp [(breg_mask hc).symm]), hu.mask]

/-- The bytes of a XOR of vectors. -/
theorem st_xor (a b : BitVec 128) :
    (aesState (a ^^^ b)).toList = Spec.Cbc.xor (aesState a).toList (aesState b).toList := by
  apply List.ext_getElem (by simp [Spec.Cbc.xor])
  intro i h₁ h₂
  have hi : i < 16 := by simpa using h₁
  have e := aesState_byte (a ^^^ b) hi
  rw [VG.Proof.Aes.toBytes_xor _ _ hi, ← aesState_byte a hi, ← aesState_byte b hi] at e
  simp only [Spec.Cbc.xor, List.getElem_zipWith]
  simpa [Vector.getD, hi] using e

theorem ofFn_toList (x : Spec.Aes.State) : (Vector.ofFn fun i : Fin 16 => x.toList.getD i.1 0) = x := by
  apply Vector.ext
  intro i hi
  simp

theorem pres_ne {r : Reg} (hr : r ∈ preserved) :
    r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by
  revert hr; cases r <;> decide

theorem cBlk16 {s₀ : State} (hp : UPre s₀) {i : Nat} (hi : i < N s₀) : (dataR s₀).Contains (blk s₀ i) 16 := by
  have := hp.data_wrap
  exact Offset.contains_base _ (by omega) (by omega)

theorem cSl16 (s₀ : State) {j : Nat} (hj : j < 8) : (scrR s₀).Contains (sl s₀ j) 16 :=
  Offset.contains_base _ (by simp only [slot]; omega) (by simp only [slot]; omega)


theorem inputs_of_local {nr : Nat} {gs : List Reg} {vs : List VReg} {u x : State} (h : Inputs nr u)
    (hl : Local gs vs u x) (h0 : .r0 ∉ gs) (h3 : .r3 ∉ gs) (h4 : .r4 ∉ gs) (hm : mask ∉ vs) : Inputs nr x :=
  ⟨(hl.keep.gpr h0).trans h.zero, (hl.v _ hm).trans h.mask, (hl.keep.gpr h4).trans h.rounds, h.min, h.max,
    fun j hj => by rw [hl.keep.2.1, hl.keep.2.2, hl.keep.gpr h3]; exact h.reads j hj⟩

/-- After the rounds' registers are set up and the eight blocks at `r17`
read. -/
structure Read8 (s₀ : State) (k : Nat) (t u : State) : Prop where
  g : ∀ r ∈ preserved, u.gpr r = t.gpr r
  r6 : u.gpr .r6 = blk s₀ k
  r3 : u.gpr .r3 = W s₀
  inp : Inputs (R s₀) u
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  mem : u.mem = t.mem
  val : ∀ j < 8, u.vpr (breg j) = rev128 (t.mem.read (blk s₀ (k + j)) 16)

theorem read8_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {t : State}
    (r14 : t.gpr .r14 = W s₀) (r15 : t.gpr .r15 = s₀.gpr .r4) (r17 : t.gpr .r17 = blk s₀ k)
    (hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀]) {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ u, Read8 s₀ k t u → WP isa (.block rest) u Φ) :
    WP isa (.block (vsetup ++ ((batchRegs 8).flatMap (Impl.Aes.PPC64LE.Crypto.readBlock false) ++
      (.subi .r6 .r6 128 :: rest)))) t Φ := by
  simp only [vsetup, Impl.AesCbc.PPC64LE.mov, List.cons_append, List.nil_append]
  refine wp_mr fun t₁ u₁ => wp_mr fun t₂ u₂ => wp_mr fun t₃ u₃ => ?_
  have g₃ (r : Reg) (h3 : r ≠ .r3) (h4 : r ≠ .r4) (h6 : r ≠ .r6) : t₃.gpr r = t.gpr r := by
    rw [u₃.other r h6, u₂.other r h4, u₁.other r h3]
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : t₃.rd = t.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  rw [WP.block_append_iff]
  refine WP.mono (Proof.Aes.PPC64LE.Crypto.setup_ok t₃) fun t₄ ⟨h0, hm, _, hl₄⟩ => ?_
  have rw₄ : t₄.rd ++ t₄.wr = t.rd ++ t.wr := by rw [hl₄.keep.2.1, hl₄.keep.2.2, rd₃, wr₃]
  have r6₄ : t₄.gpr .r6 = blk s₀ k := by
    rw [hl₄.keep.gpr (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r17]
  rw [← List.singleton_append, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (?_ : WP isa (.block ((batchRegs 8).flatMap (Impl.Aes.PPC64LE.Crypto.readBlock false) ++
      [.subi .r6 .r6 128])) t₄ (BatchRead false t₄ 8)) fun u hb => cont u ?_
  · refine Proof.Aes.PPC64LE.Crypto.batch_read_ok false 8 t₄ (by decide) h0 hm (fun e => absurd e (by decide))
      fun i hi => ?_
    rw [rw₄, hR, r6₄, blk_add]
    exact in_rw (by simp) (cBlk16 hp (by omega))
  have hR₀ := hp.rounds
  have hm₄ : t₄.mem = t.mem := by rw [hl₄.mem, m₃]
  refine ⟨fun r hr => ?_, by rw [hb.ptr, r6₄], ?_, ⟨?_, ?_, ?_, by rcases hR₀ with e | e | e <;> omega,
    by rcases hR₀ with e | e | e <;> omega, fun j hj => ?_⟩, ?_, ?_, by rw [hb.effects.mem, hm₄],
    fun j hj => ?_⟩
  · obtain ⟨h0, h3, h4, h6, -, h8, -, -, h11, h12⟩ := pres_ne hr
    rw [hb.effects.keep.gpr (by simp [h6, h8]), hl₄.keep.gpr (by simp [h0, h11, h12]), g₃ r h3 h4 h6]
  · rw [hb.effects.keep.gpr (by decide), hl₄.keep.gpr (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, r14]
  · exact (hb.effects.keep.gpr (by decide)).trans h0
  · exact (hb.effects.v _ (by simp [(batchFacts ⟨8, by decide⟩).2.2.1])).trans hm
  · rw [hb.effects.keep.gpr (by decide), hl₄.keep.gpr (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), r15]
    exact ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm
  · rw [hb.effects.keep.2.1, hb.effects.keep.2.2, rw₄, hR, hb.effects.keep.gpr (by decide),
      hl₄.keep.gpr (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, r14]
    have : j ≤ 14 := by rcases hR₀ with e | e | e <;> omega
    exact in_rw (r := schR s₀) (by simp) (Offset.contains_base (d := 16 * j) (n := 16) (k := 240) _ (by omega)
      (by omega))
  · rw [hb.effects.keep.2.1, hl₄.keep.2.1, rd₃]
  · rw [hb.effects.keep.2.2, hl₄.keep.2.2, wr₃]
  · rw [hb.val j hj, readValue, ite_eq_right (by decide), r6₄, blk_add, hm₄]

end VG.Proof.AesCbc.PPC64LE
