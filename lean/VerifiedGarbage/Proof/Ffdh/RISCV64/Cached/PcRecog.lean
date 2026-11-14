module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.VettedValidation.Verified
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Ffdh.RISCV64.ZMask
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
-- separate module: the vetted groups' recognition with its value, which only the precompute uses

/-! # The vetted groups' recognition on RISC-V, with its value

`recognize_val`: `recognize` leaves in `a5` the or of the widths of the
groups the domain matches (`orBits`), which is the first match's
(`recognizeList`), as the groups of one length have one width. -/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.VettedValidation

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Impl.Ffdh.RISCV64.VettedValidation VG.Impl.Ffdh.VettedGroups

/-- The or of the widths of the groups of `gs` the domain matches. -/
def orBits (k : Nat) (dom : List Byte) : List Group → BitVec 64
  | [] => 0
  | g :: gs => BitVec.ofNat 64 (if Hit g k dom then g.bits else 0) ||| orBits k dom gs

theorem mask_bits (b : Bool) (n : Nat) :
    bmask b &&& BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 (if b then n else 0) := by
  cases b
  · simp [bmask]
  · rw [show bmask true = BitVec.allOnes 64 from rfl, BitVec.allOnes_and, BitVec.ofInt_natCast]
    rfl

/-- `accumulate g` and `advance n`: `a5 |= g.bits` if `t4 = 0`. -/
theorem acc_val (g : Group) {n : Nat} (hb : g.bits < 2048) (hn : n ≤ 4000) (s : State) :
    WP isa (.block (accumulate g ++ advance n)) s fun t =>
      t.gpr .a5 = s.gpr .a5 ||| BitVec.ofNat 64 (if s.gpr .t4 = 0 then g.bits else 0) ∧
        t.gpr .t5 = s.gpr .t5 + BitVec.ofNat 64 n ∧ t.mem = s.mem ∧ Keep [.t6, .a5, .t5] s t := by
  refine WP.mono (WP.keep [.t6, .a5, .t5] (Q := fun t => t.gpr .a5 = s.gpr .a5 |||
      ((if BitVec.ofNat 64 0 < s.gpr .t4 then (1 : BitVec 64) else 0) - BitVec.ofNat 64 1 &&&
        BitVec.ofInt 64 (g.bits : Int)) ∧
      t.gpr .t5 = VG.Proof.Mont.off (s.gpr .t5) (n / 2 + (n - n / 2)) ∧ t.mem = s.mem)
    (by unfold accumulate advance; brun [exec_li, exec_logicImm (show imm12 (g.bits : Int) by unfold imm12; omega),
      show n / 2 < 2048 by omega, show n - n / 2 < 2048 by omega]) (by rfl) (by rfl))
    fun t ⟨⟨t5', t5, tm⟩, tk⟩ => ⟨?_, ?_, tm, tk⟩
  · rw [t5', VG.Proof.Ffdh.RISCV64.sltu_mask, mask_bits _ _]
    simp only [decide_eq_true_eq]
  · rw [t5]
    show s.gpr .t5 + BitVec.ofNat 64 (n / 2 + (n - n / 2)) = _
    congr 2
    omega

/-- The scan: `a5 |=` the widths of the groups of `gs` the domain matches. -/
theorem scan_val {src : Addr} {k : Nat} {dom : List Byte} :
    ∀ (gs : List Group) (s : State), Ctx src k dom s → TableAt (s.gpr .t5) gs s →
      WP isa (scan gs) s fun t => t.gpr .a5 = s.gpr .a5 ||| orBits k dom gs ∧ t.mem = s.mem ∧
        Keep clobbers s t
  | [], s, _, _ => WP.block_nil ⟨by simp [orBits], rfl, Keep.refl _ _⟩
  | g :: gs, s, h, data => by
    have hr := data.1
    unfold scan
    refine WP.seq (WP.mono (record_ok h g hr) fun s₁ ⟨r4, m1, k1⟩ => ?_)
    refine WP.seq (WP.mono (acc_val g (n := 8 + 3 * g.len) hr.bitsFit (by have := hr.lenFit; omega) s₁)
      fun s₂ ⟨a5, t5, m2, k2⟩ => ?_)
    have hm : s₂.mem = s.mem := m2.trans m1
    have k12 := k1.trans k2
    have tail : TableAt (s₂.gpr .t5) gs s₂ := by
      rw [t5, k1.gpr (by decide)]; exact data.2.after hm k12
    refine WP.mono (scan_val gs s₂ (h.after hm k12) tail) fun t ⟨ta, tm, tk⟩ =>
      ⟨?_, tm.trans hm, (k12.trans tk).mono (by decide)⟩
    rw [ta, a5, k1.gpr (by decide), orBits, BitVec.or_assoc]
    congr 3
    by_cases hh : Hit g k dom
    · rw [ite_eq_left_iff.mpr (fun h' => absurd (r4.mpr hh) h'), ite_eq_left_iff.mpr (fun h' => absurd hh h')]
    · rw [ite_eq_right_iff.mpr (fun h' => absurd (r4.mp h') hh), ite_eq_right_iff.mpr (fun h' => absurd h' hh)]

/-- The widths of the groups of one length are one. -/
theorem groups_bits : ∀ g₁ ∈ groups, ∀ g₂ ∈ groups, g₁.len = g₂.len → g₁.bits = g₂.bits := by
  intro g₁ h₁ g₂ h₂
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases h₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The first match's width, or 0. -/
theorem recognizeList_cases {k : Nat} {dom : List Byte} :
    ∀ gs : List Group, recognizeList gs k dom = 0 ∨ ∃ g ∈ gs, Hit g k dom ∧ recognizeList gs k dom = g.bits
  | [] => Or.inl rfl
  | g :: gs => by
    by_cases hh : Hit g k dom
    · have e : recognizeList (g :: gs) k dom = g.bits := by
        simp only [recognizeList]; exact ite_eq_left_iff.mpr (fun h' => absurd hh h')
      exact Or.inr ⟨g, List.mem_cons_self, hh, e⟩
    · have e : recognizeList (g :: gs) k dom = recognizeList gs k dom := by
        simp only [recognizeList]; exact ite_eq_right_iff.mpr (fun h' => absurd h' hh)
      rcases recognizeList_cases gs with h | ⟨g', hg', hh', e'⟩
      · exact Or.inl (e.trans h)
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', hh', e.trans e'⟩

theorem orBits_eq {k : Nat} {dom : List Byte} :
    ∀ gs : List Group, (∀ g₁ ∈ gs, ∀ g₂ ∈ gs, g₁.len = g₂.len → g₁.bits = g₂.bits) →
      orBits k dom gs = BitVec.ofNat 64 (recognizeList gs k dom)
  | [], _ => rfl
  | g :: gs, hs => by
    have ih := orBits_eq (k := k) (dom := dom) gs fun a ha b hb => hs a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    rw [orBits, ih]
    by_cases hh : Hit g k dom
    · have e : recognizeList (g :: gs) k dom = g.bits := by
        simp only [recognizeList]; exact ite_eq_left_iff.mpr (fun h' => absurd hh h')
      rw [e, ite_eq_left_iff.mpr (fun h' => absurd hh h')]
      rcases recognizeList_cases (k := k) (dom := dom) gs with h | ⟨g', hg', hh', e'⟩
      · rw [h, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.or_zero]
      · rw [e', ← hs g List.mem_cons_self g' (List.mem_cons_of_mem _ hg') (hh.1.trans hh'.1.symm),
          BitVec.or_self]
    · have e : recognizeList (g :: gs) k dom = recognizeList gs k dom := by
        simp only [recognizeList]; exact ite_eq_right_iff.mpr (fun h' => absurd h' hh)
      rw [e, ite_eq_right_iff.mpr (fun h' => absurd h' hh), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.zero_or]

/-- `recognize`: `a5 :=` the domain's recognized width. -/
theorem recognize_val {s : State} {src : Addr} {k : Nat} {dom : List Byte} (input : Ctx src k dom s)
    (table : TableAt (s.syms tableSym) groups s) :
    WP isa recognize s fun t =>
      t.gpr .a5 = BitVec.ofNat 64 (recognizeList groups k dom) ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  unfold recognize
  refine WP.seq (WP.mono (WP.keep [.t5, .a5] (Q := fun t => t.gpr .t5 = s.syms tableSym ∧ t.gpr .a5 = 0 ∧
    t.mem = s.mem) (by brun [exec_lla, exec_li]; rfl) (by rfl) (by rfl)) fun u ⟨⟨u5, ua, m⟩, k⟩ => ?_)
  refine WP.mono (scan_val groups u (input.after m k) (by rw [u5]; exact table.after m k)) fun t ⟨ta, tm, tk⟩ =>
    ⟨by rw [ta, ua, show (0 : BitVec 64) = 0#64 from rfl, BitVec.zero_or, orBits_eq groups groups_bits], tm.trans m, (k.trans tk).mono (by decide)⟩

/-- The table's records at `s`, from its bytes there. -/
theorem table_at {s : State} (read : InRegions (s.rd ++ s.wr) (s.syms tableSym) tableBytes.length)
    (bytes : Spec.Rsa.bytesAt s.mem (s.syms tableSym) tableBytes.length = tableBytes) :
    TableAt (s.syms tableSym) groups s := by
  apply tableOfBytes groups _ s read bytes
    (by change tableBytes.length ≤ 17744; rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length])
  intro g hg
  simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The table's bytes, from the contract's table. -/
theorem consts_bytes {s : State} {st : Nat} (hc : ConstsOk tableConsts st s) :
    InRegions (s.rd ++ s.wr) (s.syms tableSym) tableBytes.length ∧
      Spec.Rsa.bytesAt s.mem (s.syms tableSym) tableBytes.length = tableBytes := by
  have held := ConstsOk.held1 (name := tableSym) (ws := tableWords) hc
  refine ⟨?_, ?_⟩
  · have := ConstsOk.rd1 (name := tableSym) (ws := tableWords) hc
    rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at this
    rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length]
    exact ⟨_, List.mem_append_left _ this, Region.contains_self _ _⟩
  · apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      rw [VG.Proof.Ffdh.VettedTableFacts.table_held_byte held hj]
      exact (List.getElem_eq_getD (h := hj) 0).symm

end VG.Proof.Ffdh.RISCV64.VettedValidation
