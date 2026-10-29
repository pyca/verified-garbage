module
public import VerifiedGarbage.Impl.Sm4.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Sm4.RISCV64.Crypt16
public import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad

import VerifiedGarbage.Proof.Sm4.RISCV64.KeyInit
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Sm4.RISCV64.Keys
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit

/-!
# The loop of the SM4 key schedule on RISCV64

Each iteration runs four rounds of the key schedule (`rounds4_ok .key`),
puts the state's words in the tail buffer as a block (`fromBs_step`), and
stores them to the schedule as little-endian words (`extract_ok`): the
first block's 64-bit words, byte-reversed (stored big-endian a byte at a
time, `storeBE`). As on PPC64LE (`Proof/Sm4/PPC64LE/KeyLoop.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR ldS stS)
open VG.Impl.Words.RISCV64 (storeBE)
open VG.RISCV64.ByteLoad (beBytes)
open VG.WriteBytes (writeBytes writeBytes_frame)
open VG.Proof.Aes.RISCV64 (sboxWrites)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_outBlock' ofInt_nat)

/-! ## Bytes -/

/-- A byte of a big-endian word written. -/
theorem beBytes_byte (m : Mem) (q : Addr) (x : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    ((writeBytes m q (beBytes 8 x)) (q + BitVec.ofNat 64 t)).getLsbD j = x.getLsbD (8 * (7 - t) + j) := by
  simp only [writeBytes, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, ByteLoad.beBytes_length]
  rw [Nat.mod_eq_of_lt (by omega_arith)]
  simp only [ht, ↓reduceIte, beBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
    Option.map_some, Option.getD_some, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  simp only [hj, decide_true, Bool.true_and]

/-- A byte outside the bytes written. -/
theorem writeBytes_other (m : Mem) (q x : Addr) (xs : List Byte) (h : ¬ (x - q).toNat < xs.length) :
    writeBytes m q xs x = m x := by
  simp only [writeBytes, h, ite_false]

/-- `storeBE 8 t0 t1 a1 off`. -/
theorem storeBE8_ok (s : State) {off : Nat} (ho : off + 8 ≤ 2048)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 (off + j)) 1) :
    ∃ s', runBlock isa (storeBE 8 t0 t1 .a1 off) s = some s' ∧
      s'.mem = writeBytes s.mem (s.gpr .a1 + BitVec.ofNat 64 off) (beBytes 8 (s.gpr t0)) ∧
      (∀ r, r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', h'⟩ := Interleave.runBlock_of_WP (ByteLoad.storeBE_ok (s := s) (v := t0) (tmp := t1) (n := .a1)
    (off := off) (w := 8) (by decide) (by decide) (by decide) (by decide) ho hw)
  subst h'
  exact ⟨_, e', rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl⟩

/-- A byte of the tail buffer's block `0`. -/
theorem tail_byte (s : State) {h t j : Nat} (hh : h < 2) (ht : t < 8) (hj : j < 8) :
    (slotW s (tailAt 0 h)).getLsbD (8 * t + j) = ((tailBlock s 0)[8 * h + t]'(by omega_arith)).getLsbD j := by
  rw [slotW, readW64_bit _ _ ht hj]
  simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn, wordAddr, addr_add, tailAt]
  rw [show 8 * (tailSlot + 2 * 0 + h) + t = 8 * tailSlot + 16 * 0 + (8 * h + t) by omega_arith]

/-! ## The extraction -/

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian. -/
theorem extract_ok {s : State} {b S : Addr} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b) (hal : b.toNat % 8 = 0)
    (ha1 : s.gpr .a1 = S + BitVec.ofNat 64 (16 * m))
    (hS : ∀ t < 16, InRegions s.wr (S + BitVec.ofNat 64 (16 * m + t)) 1)
    (hT : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr b (tailAt 0 t)) 8)
    (hsep : ∀ t < 2, Region.Disjoint ⟨wordAddr b (tailAt 0 t), 8⟩ ⟨S + BitVec.ofNat 64 (16 * m), 16⟩) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (S + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0)[15 - t]'(by omega_arith)).getLsbD j) ∧
      Frame [⟨S + BitVec.ofNat 64 (16 * m), 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hal' : (s.gpr sb).toNat % 8 = 0 := by rw [hb]; exact hal
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := t0) (k := tailAt 0 1)
    (by simp only [tailAt, tailSlot_eq]; omega_arith) hal' (by rw [hb]; exact hT 1 (by decide)) rfl
  have ha1₁ : s₁.gpr .a1 = S + BitVec.ofNat 64 (16 * m) := by rw [o₁ _ (by decide), ha1]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeBE8_ok s₁ (off := 0) (by decide) fun j hj => by
    rw [wr₁, ha1₁, addr_add, Nat.zero_add]; exact hS j (by omega_arith)
  have hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), o₁ _ (by decide), hb]
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := ldMask_ok (s := s₃) (r := t0) (k := tailAt 0 0)
    (by simp only [tailAt, tailSlot_eq]; omega_arith) (by rw [hb₃]; exact hal)
    (by rw [rd₃, wr₃, rd₁, wr₁, hb₃]; exact hT 0 (by decide)) rfl
  have ha1₄ : s₄.gpr .a1 = S + BitVec.ofNat 64 (16 * m) := by
    rw [o₄ _ (by decide), g₃ _ (by decide), ha1₁]
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := storeBE8_ok s₄ (off := 8) (by decide) fun j hj => by
    rw [wr₄, wr₃, wr₁, ha1₄, addr_add]; exact hS (8 + j) (by omega_arith)
  have hW₃ : s₃.mem = writeBytes s.mem (S + BitVec.ofNat 64 (16 * m)) (beBytes 8 (slotW s (tailAt 0 1))) := by
    rw [m₃, ha1₁, v₁, m₁, addr_add, Nat.add_zero]
  have q0 : s₄.gpr t0 = slotW s (tailAt 0 0) := by
    rw [v₄]
    simp only [slotW, hb₃, hb, hW₃]
    exact (writeBytes_frame _ _ _ (Region.contains_self _ _)).readW (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep 0 (by decide)).sub_right (Region.sub_prefix (by simp [ByteLoad.beBytes_length])))
      (by decide)
  have hm6 : s₆.mem = writeBytes (writeBytes s.mem (S + BitVec.ofNat 64 (16 * m)) (beBytes 8 (slotW s (tailAt 0 1))))
      (S + BitVec.ofNat 64 (16 * m + 8)) (beBytes 8 (slotW s (tailAt 0 0))) := by
    rw [m₆, m₄, hW₃, ha1₄, q0, addr_add]
  refine ⟨s₆, ?_, fun t ht j hj => ?_, ?_, fun r hr h1 => ?_, by rw [rd₆, rd₄, rd₃, rd₁],
    by rw [wr₆, wr₄, wr₃, wr₁]⟩
  · rw [extract, Interleave.runBlock_append, Interleave.runBlock_append, Interleave.runBlock_append,
      e₁, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₆]
  · rw [hm6]
    by_cases h8 : t < 8
    · rw [writeBytes_other _ _ _ _ (by
          rw [ByteLoad.beBytes_length]
          exact VG.Proof.Sm4.off_sub_not S (n := 8) (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)),
        ← addr_add, beBytes_byte _ _ _ h8 hj, show 8 * (7 - t) + j = 8 * (7 - t) + j from rfl,
        tail_byte s (by decide) (by omega_arith) hj]
      simp only [show 8 * 1 + (7 - t) = 15 - t by omega_arith]
    · rw [show S + BitVec.ofNat 64 (16 * m + t) = S + BitVec.ofNat 64 (16 * m + 8) + BitVec.ofNat 64 (t - 8) by
          rw [addr_add, show 16 * m + 8 + (t - 8) = 16 * m + t by omega_arith], beBytes_byte _ _ _ (by omega_arith) hj,
        tail_byte s (by decide) (by omega_arith) hj]
      simp only [show 8 * 0 + (7 - (t - 8)) = 15 - t by omega_arith]
  · rw [hm6]
    exact (writeBytes_frame _ _ _ (by
        rw [ByteLoad.beBytes_length]; exact VG.Offset.contains S (by omega_arith) (by omega_arith) (by omega_arith))).trans
      (writeBytes_frame _ _ _ (by
        rw [ByteLoad.beBytes_length]; exact VG.Offset.contains S (by omega_arith) (by omega_arith) (by omega_arith)))
  · rw [g₆ r h1, o₄ r hr, g₃ r h1, o₁ r hr]

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : Addr) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  a1 : s.gpr .a1 = S + BitVec.ofNat 64 (16 * m)
  a4 : s.gpr .a4 = b + BitVec.ofNat 64 (8 * tableEnd)
  kr : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  masks : MasksOk s
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (S + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b, 8 * slots⟩, ⟨S, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ra : s.gpr .ra = s₀.gpr .ra

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : Addr) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  sch : (⟨S, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 128⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitS : S.toNat + 128 ≤ 2 ^ 64
  al : b.toNat % 8 = 0

theorem ekIter_ok {s₀ : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧
      (s'.gpr t0 == 0) = decide (m + 1 = 8) := by
  have hfit := hp.fit
  have hfitS := hp.fitS
  rw [slots_eq] at hfit
  -- `ra` to its slot.
  obtain ⟨sA, eA, svA, gA, rdA, wrA, fA⟩ := saveAux_ok (s := s) (b := b) (by rw [hi.wr]; exact hp.scr)
    hi.base hp.al
  have bA : sA.gpr sb = s.gpr sb := gA _ (by decide)
  rw [← hi.base] at fA
  have hkA : KeyCtx sA Spec.Sm4.ck := hi.keys.of_auxFrame bA wrA fA
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hkA (CtxW.refl (hi.masks.of_auxFrame bA fA))
    (by rw [AtEntry, gA _ (by decide), bA, hi.base]; exact hi.kr) hm (hi.st.of_auxFrame bA fA)
  -- `ra` back.
  obtain ⟨sR, eR, gR, oR, mR, rdR, wrR⟩ := restoreAux_ok (s₀ := s) (s := s₁) (b := b)
    (by rw [c₁.wr, wrA, hi.wr]; exact hp.scr) (by rw [c₁.base, bA, hi.base]) hp.al
    (auxSaved_frame (by rw [← hi.base, ← bA]; exact c₁.frame) svA)
  have cR : XCtx sA sR := XCtx.of_restore c₁ gA gR oR mR rdR wrR
  have kR : sR.gpr kr = s.gpr kr := by rw [oR _ (by decide) (by decide), k₁, gA _ (by decide)]
  obtain ⟨s₂, e₂, kr₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok sR 256 (by decide)
  have c₂ : XCtx sA s₂ := cR.kr o₂ m₂ rd₂ wr₂
  rw [show BitVec.ofInt 64 256 = BitVec.ofNat 64 256 from rfl] at kr₂
  have X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide), mR, oR sb (by decide) (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kr₃, X₃, T₃⟩ := fromBs_step hkA c₂ X₂
  have base₃ : s₃.gpr sb = b := by rw [c₃.base, bA, hi.base]
  have a1₃ : s₃.gpr .a1 = S + BitVec.ofNat 64 (16 * m) := by rw [c₃.keep _ (by decide) (by decide), gA _ (by decide), hi.a1]
  have wr₃ : s₃.wr = s₀.wr := by rw [c₃.wr, wrA, hi.wr]
  have rd₃ : s₃.rd = s₀.rd := by rw [c₃.rd, rdA, hi.rd]
  have inS : ∀ t < 16, InRegions s₃.wr (S + BitVec.ofNat 64 (16 * m + t)) 1 := fun t ht =>
    ⟨_, by rw [wr₃]; exact hp.sch, VG.Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  have inT : ∀ t < 2, InRegions (s₃.rd ++ s₃.wr) (wordAddr b (tailAt 0 t)) 8 := fun t ht =>
    ⟨_, List.mem_append_right _ (by rw [wr₃]; exact hp.scr), by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [tailAt, tailSlot_eq, slots_eq]; omega_arith)
        (by rw [tailAt, tailSlot_eq]; omega_arith)⟩
  have sepTS : ∀ k < slots, Region.Disjoint ⟨wordAddr b k, 8⟩ ⟨S + BitVec.ofNat 64 (16 * m), 16⟩ := fun k hk =>
    (hp.sep.sub_left (VG.Offset.sub_base S (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq] at hk ⊢; omega_arith)) |>.symm
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, f₄, o₄, rd₄, wr₄⟩ := extract_ok hm base₃ hp.al a1₃ inS inT
    (fun t ht => sepTS _ (by have := tailAt_lt (b := 0) (by decide) ht; rw [tableSlot_eq] at this; rw [slots_eq]; omega_arith))
  have keep₄ : ∀ k < slots, slotW s₄ k = slotW s₃ k := fun k hk => by
    simp only [slotW, o₄ sb (by decide) (by decide), base₃]
    exact f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sepTS k hk) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .a1 .a1 (imm := 16) (by decide)
  rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl] at r₅
  obtain ⟨sQ, eQ, rQ, oQ, mQ, rdQ, wrQ⟩ := slotAddr_ok s₅ .a4 tableEnd
  obtain ⟨s₆, e₆, z₆, g₆, m₆, rd₆, wr₆⟩ := subR_ok sQ t0 kr .a4
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, mQ, m₅]
  have g₆' : ∀ r, r ≠ .a1 → r ≠ t0 → r ≠ t1 → r ≠ .a4 → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₆ r h2, oQ r h4, o₅ r h1, o₄ r h2 h3]
  have base₆ : s₆.gpr sb = b := by rw [g₆' _ (by decide) (by decide) (by decide) (by decide), base₃]
  have keep₆ : ∀ k < slots, slotW s₆ k = slotW s₃ k := fun k hk => by
    rw [← keep₄ k hk]; simp only [slotW, mem₆, g₆' sb (by decide) (by decide) (by decide) (by decide), o₄ sb (by decide) (by decide)]
  have kr₆ : AtEntry s₆ b (4 * (m + 1)) := by
    rw [AtEntry, g₆' _ (by decide) (by decide) (by decide) (by decide), kr₃, kr₂, kR, show s.gpr kr = _ from hi.kr, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith]
  have rdi₆ : s₆.gpr .a4 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₆ _ (by decide), rQ, o₅ sb (by decide), o₄ sb (by decide) (by decide), base₃]
  have hent : ∀ (st : State) e j, entryW st.mem (st.gpr sb) e j = slotW st (tableSlot + 8 * e + j) := fun st e j => by
    simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]
  have key₃ := hkA.of_ctx c₃
  -- The schedule's bytes outside this iteration's.
  have old₆ : ∀ x, (∀ r ∈ [(⟨b, 8 * tableSlot⟩ : Region), auxR b, ⟨S + BitVec.ofNat 64 (16 * m), 16⟩],
      ¬ r.Contains x 1) → s₆.mem x = s.mem x := fun x hx => by
    rw [mem₆, f₄ x (fun r hr => hx r (by simp at hr; simp [hr])),
      c₃.frame x (fun r hr => by simp at hr; subst hr; rw [bA, hi.base]; exact hx _ (by simp)),
      fA x (fun r hr => by simp at hr; subst hr; rw [hi.base]; exact hx _ (by simp))]
  refine ⟨s₆, ?_, ⟨base₆, ?_,
    rdi₆, kr₆, ⟨by rw [base₆, wr₆, wrQ, wr₅, wr₄, wr₃]; exact hp.scr, by rw [base₆]; rw [slots_eq]; exact hfit,
      by rw [base₆]; exact hp.al,
      fun e he => (key₃.keys e he).congr fun j hj => by
        rw [hent s₆, hent s₃, keep₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith)]⟩,
    fun kv hkv => by rw [keep₆ _ (by have := mask_lt hkv; rw [slots_eq]; omega_arith)]; exact c₃.masks kv hkv,
    fun w hw => (X₃ w hw).congr fun j hj => keep₆ _ (by simp only [stateSlot, slots_eq]; omega_arith),
    fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_, by rw [rd₆, rdQ, rd₅, rd₄, rd₃], by rw [wr₆, wrQ, wr₅, wr₄, wr₃],
    by rw [g₆' _ (by decide) (by decide) (by decide) (by decide), c₃.keep _ (by decide) (by decide), gA _ (by decide),
      hi.ra]⟩, ?_⟩
  · rw [keyBody, Interleave.runBlock_append, Interleave.runBlock_append, Interleave.runBlock_append,
      Interleave.runBlock_append, Interleave.runBlock_append, Interleave.runBlock_append,
      Interleave.runBlock_append, Interleave.runBlock_append, eA, Option.bind_some,
      e₁, Option.bind_some, eR, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some, eQ, Option.bind_some, e₆]
  · rw [g₆ _ (by decide), oQ _ (by decide), r₅, o₄ _ (by decide) (by decide), a1₃, addr_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega_arith
      have hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega_arith] at hB
      rw [mem₆, hB, T₃ 0 (by decide), getLsbD_outBlock' _ _ hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega_arith, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega_arith,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega_arith]
    · rw [old₆ _ (fun r hr => ?_)]
      · exact hi.sched i (by omega_arith) c hc j hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · intro hc'
          exact hp.sep (S + BitVec.ofNat 64 (4 * i + c)) (VG.Offset.contains_base S (by omega_arith) (by omega_arith))
            (Region.sub_prefix (show 8 * tableSlot ≤ 8 * slots by rw [tableSlot_eq, slots_eq]; omega_arith) _ hc')
        · intro hc'
          exact hp.sep (S + BitVec.ofNat 64 (4 * i + c)) (VG.Offset.contains_base S (by omega_arith) (by omega_arith))
            (VG.Offset.sub_base b (by rw [auxSlot_eq, slots_eq]) _ hc')
        · exact VG.Proof.Sm4.not_contains_off S (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    have h1 : s₆.mem.readW (wordAddr b (savedSlot + i)) 64 = s₃.mem.readW (wordAddr b (savedSlot + i)) 64 := by
      have := keep₆ _ hk; simp only [slotW, base₆, base₃] at this; exact this
    have h2 : s₃.mem.readW (wordAddr b (savedSlot + i)) 64 = sA.mem.readW (wordAddr b (savedSlot + i)) 64 :=
      c₃.frame.readW (r := ⟨wordAddr b (savedSlot + i), 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [bA, hi.base, wordAddr]
        exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith))
        (by decide)
    have h3 := slot_auxR fA (k := savedSlot + i) (by rw [savedSlot_eq, auxSlot_eq]; omega_arith)
    rw [hi.base] at h3
    rw [h1, h2, h3]; exact hi.saved i hi'
  · rw [mem₆]
    refine hi.frame.trans ((fA.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((c₃.frame.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ⟨⟨S, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base, auxR]
      exact VG.Offset.sub_base b (by rw [auxSlot_eq, slots_eq])
    · simp only [List.mem_singleton] at hr; subst hr; rw [bA, hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base S (by omega_arith)
  · rw [z₆, rQ, oQ kr (by decide), o₅ kr (by decide), o₅ sb (by decide), o₄ kr (by decide) (by decide),
      o₄ sb (by decide) (by decide), base₃, kr₃, kr₂, kR, show s.gpr kr = _ from hi.kr, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega_arith) (by rw [tableSlot_eq]; omega_arith)]
    simp only [decide_eq_decide]; omega_arith

end VG.Proof.Sm4.RISCV64
