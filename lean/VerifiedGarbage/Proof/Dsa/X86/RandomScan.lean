module

public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Impl.Dsa.X86.Random
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# Scanning the public q for its significant bytes (x86)

`significant` reads the `q_len` bytes of q from its first, keeping the
count of bytes from the first nonzero one (`ebx`) and that byte (`edx`):
`VG.Proof.Dsa.significant`. Its branches are on q's bytes, which are public.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movzx d, byte [m]`. -/
theorem wp_load8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hr : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Upd s t d ((s.mem a).setWidth 32) → t.cf = s.cf → t.zf = s.zf → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q :=
  cons (s' := s.setReg d ((s.mem a).setWidth 32))
    (by simp only [exec, ha, State.load8, hr, ite_true, Option.map_some]) (k _ (Upd.setReg _ _ _) rfl rfl)

/-- `mov byte [m], r`. -/
theorem wp_store8 {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := {s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8)})
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- `bs` at `p`: readable bytes below `2³²`. -/
structure BytesIn (s : State) (p : BitVec 32) (bs : List Byte) : Prop where
  fit : p.toNat + bs.length ≤ 2 ^ 32
  rd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1
  val : ∀ i (h : i < bs.length), s.mem (p.setWidth 64 + BitVec.ofNat 64 i) = bs[i]

theorem BytesIn.drop {s : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs) (j : Nat)
    (hj : j ≤ bs.length) : BytesIn s (p + BitVec.ofNat 32 j) (bs.drop j) := by
  have hfit := h.fit
  have hpj : j < bs.length → (p + BitVec.ofNat 32 j).toNat = p.toNat + j := fun hj' => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega),
      Nat.mod_eq_of_lt (by omega_using [hfit, hj'])]
  have e : ∀ i, j + i < bs.length → (p + BitVec.ofNat 32 j).setWidth 64 + BitVec.ofNat 64 i =
      p.setWidth 64 + BitVec.ofNat 64 (j + i) := fun i hi => by
    have := hpj (by omega)
    rw [← addr_eq (x := p + BitVec.ofNat 32 j) (k := i) (by omega_using [this, hfit, hi]),
      ← addr_eq (x := p) (k := j + i) (by omega_using [hfit, hi])]
    simp only [addr, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.length_drop]
    by_cases hjl : j = bs.length
    · rw [hjl, Nat.sub_self, Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)
    · rw [hpj (by omega)]; omega
  · rw [List.length_drop] at hi
    rw [e i (by omega)]; exact h.rd _ (by omega)
  · rw [List.length_drop] at hi
    rw [e i (by omega), h.val _ (by omega), List.getElem_drop]

theorem BytesIn.congr {s t : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : BytesIn t p bs :=
  ⟨h.fit, fun i hi => by rw [hr, hw]; exact h.rd i hi, fun i hi => by rw [hm]; exact h.val i hi⟩

/-- The scan's pair after its byte `b`, with `remaining` bytes from it on. -/
def scanNext (found : Nat × Byte) (remaining : Nat) (b : Byte) : Nat × Byte :=
  if found.1 = 0 ∧ b ≠ 0 then (remaining, b) else found

/-- The scan's result from `found`, with `bs` to read. -/
def scanFinish (found : Nat × Byte) (bs : List Byte) : Nat × Byte :=
  if found.1 = 0 then VG.Proof.Dsa.significant bs else found

theorem scanFinish_step (found : Nat × Byte) (b : Byte) (bs : List Byte) :
    scanFinish (scanNext found (bs.length + 1) b) bs = scanFinish found (b :: bs) := by
  by_cases hf : found.1 = 0
  · by_cases hb : b = 0
    · have h1 : scanNext found (bs.length + 1) b = found := by simp [scanNext, hb]
      rw [h1]
      simp only [scanFinish, hf, ite_true, VG.Proof.Dsa.significant, hb]
    · have h1 : scanNext found (bs.length + 1) b = (bs.length + 1, b) := by
        simp only [scanNext, hf, ne_eq, hb, not_false_eq_true, and_self, ite_true]
      rw [h1]
      simp only [scanFinish, hf, ite_true, VG.Proof.Dsa.significant, hb, ite_false, Nat.add_one_ne_zero]
  · have h1 : scanNext found (bs.length + 1) b = found := by simp [scanNext, hf]
    rw [h1]
    simp only [scanFinish, hf, ite_false]

theorem scanFinish_nil {found : Nat × Byte} (hz : found.1 = 0 → found.2 = 0) :
    scanFinish found [] = found := by
  unfold scanFinish
  split
  · rename_i h
    exact Prod.ext h.symm (hz h).symm
  · rfl

/-- The scan's state, with `rest` to read. -/
structure ScanState (s : State) (p : BitVec 32) (rest : List Byte) (found : Nat × Byte) : Prop where
  esi : s.gpr .esi = p
  ecx : s.gpr .ecx = BitVec.ofNat 32 rest.length
  ebx : s.gpr .ebx = BitVec.ofNat 32 found.1
  edx : s.gpr .edx = found.2.setWidth 32
  bytes : BytesIn s p rest
  bound : found.1 < 2 ^ 32
  zero : found.1 = 0 → found.2 = 0

theorem significantByte_ok {s : State} {p : BitVec 32} {b : Byte} {rest : List Byte} {found : Nat × Byte}
    (h : ScanState s p (b :: rest) found) (hl : rest.length + 1 < 2 ^ 32) :
    WP isa significantByte s fun t =>
      ScanState t (p + 1) rest (scanNext found (rest.length + 1) b) ∧
      t.zf = some (decide (rest.length = 0)) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have hfit := h.bytes.fit
  have hb : s.mem (p.setWidth 64) = b := by
    have := h.bytes.val 0 (by simp)
    simpa only [BitVec.add_zero, List.getElem_cons_zero] using this
  have hr : InRegions (s.rd ++ s.wr) (p.setWidth 64) 1 := by
    simpa only [BitVec.add_zero] using h.bytes.rd 0 (by simp)
  have ha : s.ea (at_ .esi 0) = p.setWidth 64 := by
    change (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, h.esi]
  unfold significantByte significantChoose
  refine WP.seq (wp_load8 ha hr fun s₁ u₁ _ _ => WP.block_nil ?_)
  rw [hb] at u₁
  have hz₁ : (s₁.gpr .ebx == 0) = decide (found.1 = 0) := by
    rw [u₁.other _ (by decide), h.ebx, ofNat_beq_zero h.bound]
  -- The choice.
  have after : ∀ (u : State) (f' : Nat × Byte), f' = scanNext found (rest.length + 1) b →
      u.gpr .ebx = BitVec.ofNat 32 f'.1 → u.gpr .edx = f'.2.setWidth 32 → u.mem = s.mem →
      Keeps [.eax, .ebx, .edx] s u →
      WP isa (.block [.alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) u fun t =>
        ScanState t (p + 1) rest (scanNext found (rest.length + 1) b) ∧
        t.zf = some (decide (rest.length = 0)) ∧ t.mem = s.mem ∧
        Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
    intro u f' hf' hbx hdx hm hk
    subst hf'
    refine wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ _ z₃ => WP.block_nil ?_
    have k₃ : Keeps [.eax, .ebx, .ecx, .edx, .esi] s s₃ :=
      ((hk.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))
    have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, hm]
    have hcx : s₃.gpr .ecx = BitVec.ofNat 32 rest.length := by
      rw [u₃.gpr, u₂.other _ (by decide), hk.1 _ (by decide), h.ecx, List.length_cons, BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    have hbnd : (scanNext found (rest.length + 1) b).1 < 2 ^ 32 ∧
        ((scanNext found (rest.length + 1) b).1 = 0 → (scanNext found (rest.length + 1) b).2 = 0) := by
      unfold scanNext
      split
      · exact ⟨hl, fun e => by simp only at e; omega⟩
      · exact ⟨h.bound, h.zero⟩
    refine ⟨⟨?_, hcx, by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact hbx,
      by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact hdx, ?_, hbnd.1, hbnd.2⟩, ?_, hm₃, k₃⟩
    · rw [u₃.other _ (by decide), u₂.gpr, hk.1 _ (by decide), h.esi]
    · have := (h.bytes.drop 1 (by simp)).congr hm₃ (by rw [k₃.2.1]) (by rw [k₃.2.2])
      rw [List.drop_one, List.tail_cons] at this; exact this
    · rw [z₃, u₂.other _ (by decide), hk.1 _ (by decide), h.ecx]
      have := sub_beq (a := rest.length + 1) (b := 1) hl (by decide)
      rw [List.length_cons, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, this]
      exact congrArg some (decide_eq_decide.mpr (by omega))
  refine WP.seq (WP.seq (wp_test fun s₂ f₂ z₂ => WP.block_nil ?_))
  rw [BitVec.and_self, hz₁] at z₂
  have k₂ : Keeps [.eax, .ebx, .edx] s s₂ := (u₁.keeps.mono (by decide)).trans (f₂.keeps _)
  by_cases hf0 : found.1 = 0
  · refine WP.ite true (by simp only [eval, z₂, hf0, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine WP.seq (wp_test fun s₃ f₃ z₃ => WP.block_nil ?_)
    have heax : s₂.gpr .eax = b.setWidth 32 := by rw [f₂.gpr, u₁.gpr]
    have hz₃ : (s₂.gpr .eax &&& s₂.gpr .eax == 0) = decide (b = 0) := by
      rw [heax, BitVec.and_self]
      by_cases hb0 : b = 0
      · subst hb0; rfl
      · simp only [hb0, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro e; apply hb0; apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide : 2 ^ 8 ≤ 2 ^ 32))] at this
        rw [this]; rfl
    rw [hz₃] at z₃
    have k₃ : Keeps [.eax, .ebx, .edx] s s₃ := k₂.trans (f₃.keeps _)
    by_cases hb0 : b = 0
    · refine WP.ite false (by simp only [eval, z₃, hb0, decide_true, Option.map_some, Bool.not_true])
        (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
      have hs : scanNext found (rest.length + 1) b = found := by simp [scanNext, hb0]
      exact after s₃ _ rfl (by rw [hs, f₃.gpr, f₂.gpr, u₁.other _ (by decide), h.ebx])
        (by rw [hs, f₃.gpr, f₂.gpr, u₁.other _ (by decide), h.edx]) (by rw [f₃.mem, f₂.mem, u₁.mem]) k₃
    · refine WP.ite true (by simp only [eval, z₃, hb0, decide_false, Option.map_some, Bool.not_false])
        (fun _ => wp_movS rfl fun s₄ u₄ _ => wp_movS rfl fun s₅ u₅ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
      have hs : scanNext found (rest.length + 1) b = (rest.length + 1, b) := by
        simp only [scanNext, hf0, ne_eq, hb0, not_false_eq_true, and_self, ite_true]
      refine after s₅ _ rfl ?_ ?_ (by rw [u₅.mem, u₄.mem, f₃.mem, f₂.mem, u₁.mem]) ?_
      · rw [hs, u₅.other _ (by decide), u₄.gpr, f₃.gpr, f₂.gpr, u₁.other _ (by decide), h.ecx]; rfl
      · rw [hs, u₅.gpr, u₄.other _ (by decide), f₃.gpr, heax]
      · exact (k₃.trans (u₄.keeps.mono (by decide))).trans (u₅.keeps.mono (by decide))
  · refine WP.ite false (by simp only [eval, z₂, hf0, decide_false]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    have hs : scanNext found (rest.length + 1) b = found := by simp [scanNext, hf0]
    exact after s₂ _ rfl (by rw [hs, f₂.gpr, u₁.other _ (by decide), h.ebx])
      (by rw [hs, f₂.gpr, u₁.other _ (by decide), h.edx]) (by rw [f₂.mem, u₁.mem]) k₂

/-- Scan a nonempty q, leading zero padding included. -/
theorem significant_ok {s : State} {p : BitVec 32} {bs : List Byte}
    (hsi : s.gpr .esi = p) (hcx : s.gpr .ecx = BitVec.ofNat 32 bs.length)
    (hb : BytesIn s p bs) (hn : 0 < bs.length) (h32 : bs.length < 2 ^ 32) :
    WP isa Random.significant s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (VG.Proof.Dsa.significant bs).1 ∧
      t.gpr .edx = (VG.Proof.Dsa.significant bs).2.setWidth 32 ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  unfold Random.significant
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => wp_movS rfl fun s₂ u₂ _ => WP.block_nil ?_)
  have k₂ : Keeps [.eax, .ebx, .ecx, .edx, .esi] s s₂ := (u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have h₀ : ScanState s₂ p bs (0, 0) :=
    ⟨by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hsi,
      by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hcx,
      by rw [u₂.other _ (by decide), u₁.gpr]; rfl, by rw [u₂.gpr]; rfl,
      hb.congr m₂ k₂.2.1 k₂.2.2, by decide, fun _ => rfl⟩
  refine WP.loop (M := isa) (fun n t => ∃ (j : Nat) (found : Nat × Byte), (bs.drop j).length = n ∧ 0 < n ∧
      ScanState t (p + BitVec.ofNat 32 j) (bs.drop j) found ∧ scanFinish found (bs.drop j) = VG.Proof.Dsa.significant bs ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t) ?_ bs.length s₂
    ⟨0, (0, 0), by simp, hn, by simpa only [BitVec.add_zero, List.drop_zero] using h₀, by simp [scanFinish],
      m₂, k₂⟩
  rintro n t ⟨j, found, hlen, hpos, ht, htarget, htm, hkt⟩
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, bs.drop j = b :: rest := by
    cases e : bs.drop j with
    | nil => rw [e] at hlen; simp at hlen; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  rw [hbr] at ht htarget hlen
  have hrl : rest.length + 1 = bs.length - j := by
    have := congrArg List.length hbr; simp only [List.length_drop, List.length_cons] at this; omega
  refine WP.mono (significantByte_ok ht (by omega))
    fun u ⟨hu, hz, hum, hku⟩ => ?_
  have hrest : bs.drop (j + 1) = rest := by
    rw [← List.drop_drop, hbr, List.drop_one, List.tail_cons]
  have hu' : ScanState u (p + BitVec.ofNat 32 (j + 1)) (bs.drop (j + 1)) (scanNext found (rest.length + 1) b) := by
    rw [hrest, BitVec.ofNat_add, ← BitVec.add_assoc]; exact hu
  have htarget' := (scanFinish_step found b rest).trans htarget
  have hk := hkt.trans hku
  by_cases he : rest.length = 0
  · left
    refine ⟨by simp only [eval, hz, he, decide_true, Option.map_some, Bool.not_true], ?_, ?_, hum.trans htm, hk⟩
    · have hnil := (congrArg (scanFinish _) (List.length_eq_zero_iff.mp he)).trans (scanFinish_nil hu.zero)
      rw [hu.ebx, ← hnil.symm.trans htarget']
    · have hnil := (congrArg (scanFinish _) (List.length_eq_zero_iff.mp he)).trans (scanFinish_nil hu.zero)
      rw [hu.edx, ← hnil.symm.trans htarget']
  · right
    refine ⟨by simp only [eval, hz, he, decide_false, Option.map_some, Bool.not_false],
      rest.length, by simp only [List.length_cons] at hlen; omega, j + 1, _, by rw [hrest], by omega,
      hu', by rw [hrest]; exact htarget', hum.trans htm, hk⟩

end VG.Proof.Dsa.X86
