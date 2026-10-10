import VerifiedGarbage.Proof.Modes.AArch64.CbcEncSteps
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.CbcEnc

/-!
# CBC encryption on AArch64, for any core: the data loop

`cbcEncBlock_wp`: one iteration encrypts block `j`, which holds
`Pⱼ ⊕ Cⱼ₋₁`, in the buffer (`encIn_ok`, `CoreSpec.crypt_wp`), stores
`Cⱼ` back (`encOut_ok`) and, unless it was the last, XORs it into block
`j + 1` (`encChain_ok`). As on x86-64 (`Proof/Modes/X86_64/CbcEncLoop.lean`).
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- A byte of the data before block `j`: the ciphertext's below it, block
`j` as `Pⱼ ⊕ Cⱼ₋₁`, the plaintext's above. -/
def encByte (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (j i : Nat) : Byte :=
  if i < 16 * j then (cbcEncC ciph m₀ D iv (i / 16)).getD (i % 16) 0
  else if i < 16 * (j + 1) then m₀ (D + BitVec.ofNat 64 i) ^^^ (cbcEncPrev ciph m₀ D iv j).getD (i - 16 * j) 0
  else m₀ (D + BitVec.ofNat 64 i)

/-- The data loop, before block `j`; `m₀` is the memory on entry. -/
structure EInv (cs : CoreSpec c) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte)
    (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (16 * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - j)
  lt : j < n
  data : ∀ i < 16 * n, s.mem (D + BitVec.ofNat 64 i) = encByte (cs.cipher k) m₀ D iv j i
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure EDone (cs : CoreSpec c) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte)
    (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv m₀ s.mem D n n (cbcEncC (cs.cipher k) m₀ D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Two stores within the 16 bytes at `a` keep the rest of memory. -/
theorem two_frame {m : Mem} {a : Addr} {v₀ v₁ : BitVec 64} :
    Frame [⟨a, 16⟩] m ((m.writeW a v₀).writeW (a + BitVec.ofNat 64 8) v₁) := fun x hx =>
  two_out fun h => hx _ List.mem_cons_self (by simp only [Region.Contains]; omega)

theorem cbcEncBlock_wp (cs : CoreSpec c) {s₀ : State} {m₀ : Mem} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 16) (hp : GPre c s₀ B D n) {j : Nat} {s : State}
    (hi : EInv cs s₀ m₀ B D n k iv j s) :
    WP isa c.cbcEncBlock s fun s' => (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ EDone cs s₀ m₀ B D n k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ EInv cs s₀ m₀ B D n k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hj := hi.lt
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  have hN : 8 * c.total < 2 ^ 64 := by omega
  have hn64 : 16 * n ≤ 2 ^ 64 := by omega
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (16 * j)
  let T := wordAddr B c.buf
  have hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subT : Region.Sub ⟨T, 16⟩ ⟨B, 8 * c.total⟩ :=
    VG.Offset.sub_base B (by omega)
  have subTbuf : Region.Sub ⟨T, 16⟩ (bufRegion c B) := VG.Offset.sub B (by omega) (by omega)
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ :=
    Region.sub_prefix (by omega)
  have subA : Region.Sub ⟨A, 16⟩ ⟨D, 16 * n⟩ := VG.Offset.sub_base D (by omega)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.total⟩ → Region.Disjoint ⟨D, 16 * n⟩ r :=
    fun h => hp.sep.sub_right h
  have dAT : Region.Disjoint ⟨A, 16⟩ ⟨T, 16⟩ := (dDS subT).sub_left subA
  have inT : ∀ w < 2, InRegions s.wr (wordAddr B (c.buf + w)) 8 := fun w hw =>
    ⟨_, hwS, VG.Offset.contains_base B (by omega) (by omega)⟩
  have inA : ∀ o, o + 8 ≤ 16 → InRegions s.wr (A + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨_, hwD, by rw [addr_add]; exact VG.Offset.contains_base D (by omega) (by omega)⟩
  -- Block `j` to the buffer.
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := encIn_ok hL d6 s hi.base hi.dataR (fun o ho => inRd (inA o ho)) inT
  unfold Core.cbcEncBlock
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have base₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hi.base]
  have f₁ : Frame [⟨T, 16⟩] s.mem s₁.mem := by rw [m₁]; exact two_frame
  have ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf) fun r hr => by
    obtain ⟨h1, -⟩ := of_not_modeRegs hr; exact g₁ r (not_own h1).1
  -- Encrypted.
  refine WP.seq (WP.mono (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hwS, hfit⟩ ready₁)
    fun s₂ ⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩ => ?_)
  have eT : bufAddr c B 0 = T := by simp only [bufAddr, T, wordAddr, Nat.mul_zero, Nat.add_zero]
  -- The bytes of block `j`, and its encryption.
  have blk : bytesAt s.mem A 16 = Spec.Cbc.xor (bytesAt m₀ A 16) (cbcEncPrev ciph m₀ D iv j) := by
    have hpl : (cbcEncPrev ciph m₀ D iv j).length = 16 := by
      unfold cbcEncPrev; split
      · exact hiv
      · generalize j - 1 = t; cases t <;> exact cs.cipher_len k _
    apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor, hpl])
    intro u h1 _
    have hu : u < 16 := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range, Spec.Cbc.xor, List.getElem_zipWith]
    rw [addr_add, hi.data _ (by omega), encByte, ite_eq_right (by omega), ite_eq_left (by omega),
      show 16 * j + u - 16 * j = u by omega, ← List.getElem_eq_getD (h := by rw [hpl]; exact hu)]
  have C₂ : ∀ u < 16, s₂.mem (T + BitVec.ofNat 64 u) = (cbcEncC ciph m₀ D iv j).getD u 0 := fun u hu => by
    rw [← bytesAt_getD s₂.mem T hu, ← eT, ks₂ 0 hL.G_pos, eT]
    congr 2
    rw [cbcEncC_eq]
    congr 1
    rw [← blk]
    apply List.ext_getElem (by simp [bytesAt])
    intro v h1 _
    have hv : v < 16 := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [m₁, copy16_in s.mem dAT.symm hv]
  -- Back to the data, and the count.
  obtain ⟨s₃, e₃, m₃, l₃, g₃, rd₃, wr₃⟩ := encOut_ok hL d6 l6 s₂ base₂ (by rw [dr₂, g₁ _ d6, hi.dataR])
    (fun w hw => by rw [rd₂, wr₂, rd₁, wr₁]; exact inRd (inT w hw))
    (fun o ho => by rw [wr₂, wr₁]; exact inA o ho)
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have left₃ : s₃.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₃, lr₂, g₁ _ l6, hi.leftR, VG.Offset.ofNat_sub_ofNat (by omega), show n - j - 1 = n - (j + 1) by omega]
  have hz₃ : isa.eval (.zero .x c.leftReg) s₃ = some (decide (j + 1 = n)) := by
    rw [eval_zero, left₃, ofNat_beq_zero (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  have base₃ : s₃.gpr sb = B := by rw [g₃ _ (by decide) (Ne.symm lsb), base₂]
  have data₃ : s₃.gpr c.dataReg = A := by rw [g₃ _ d6 hdl, dr₂, g₁ _ d6, hi.dataR]
  have f₃ : Frame [⟨A, 16⟩] s₂.mem s₃.mem := by rw [m₃]; exact two_frame
  have A₃ : ∀ u < 16, s₃.mem (A + BitVec.ofNat 64 u) = (cbcEncC ciph m₀ D iv j).getD u 0 := fun u hu => by
    rw [m₃, copy16_in s₂.mem dAT hu, C₂ u hu]
  -- The data outside block `j` and the buffer, through the encryption.
  have outCore : ∀ i < 16 * n, s₂.mem (D + BitVec.ofNat 64 i) = s₁.mem (D + BitVec.ofNat 64 i) := fun i hin =>
    f₂.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS subCore)
      hn64 hin
  have outT : ∀ i < 16 * n, s₁.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin =>
    f₁.bytes (R := ⟨D, 16 * n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS subT)
      hn64 hin
  have outA : ∀ i, i < 16 * j ∨ 16 * (j + 1) ≤ i → i < 16 * n →
      s₃.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i h1 h2 => by
    rw [f₃ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D h1 (by omega) (by decide) (by omega)), outCore i h2, outT i h2]
  -- The slots.
  have slotOut : ∀ i < 10, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ ⟨T, 16⟩ ∧
      Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) ∧
      ∀ {R : Region}, Region.Sub R ⟨D, 16 * n⟩ → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi6 =>
    ⟨VG.Offset.disjoint B (by omega) (by omega) (by omega), VG.Offset.disjoint_base B (by omega) (by omega),
      fun h => ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.total by
        omega))).sub_left h).symm⟩
  have saved₃ : ∀ i < 10, s₃.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi6 => by
    obtain ⟨d1, d2, d3⟩ := slotOut i hi6
    rw [← hi.saved i hi6]
    refine (f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d3 subA) (by decide)).trans ?_
    refine (f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d2) (by decide)).trans ?_
    exact f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact d1) (by decide)
  have fr₃ : Frame [⟨B, 8 * c.total⟩, ⟨D, 16 * n⟩] s₀.mem s₃.mem :=
    hi.frame.trans (((f₁.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₂.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans
      (f₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subA⟩))
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, rd₁, hi.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁, hi.wr]
  have ready₃ : cs.Ready s₃ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inl ((dDS subCore).sub_left subA).symm) fun r hr => by
    obtain ⟨h1, -, h3⟩ := of_not_modeRegs hr; exact g₃ r (not_own h1).1 h3
  -- The last block, or on to the next.
  have inN : ∀ o, o + 8 ≤ 16 → j + 1 < n → InRegions s₃.wr (A + BitVec.ofNat 64 (16 + o)) 8 := fun o ho hjn => by
    rw [wr₃', ← hi.wr]
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega) (by omega)
  refine WP.seq (WP.mono (M := isa) (Q := fun s₄ => (∀ x, x ≠ .x6 → x ≠ .x7 → s₄.gpr x = s₃.gpr x) ∧ s₄.rd = s₃.rd ∧
      s₄.wr = s₃.wr ∧ (j + 1 = n → s₄.mem = s₃.mem) ∧
      (j + 1 < n → s₄.mem = xor16 s₃.mem (A + BitVec.ofNat 64 16) T))
    (WP.ite (decide (j + 1 = n)) hz₃ (fun h => ?_) (fun h => ?_)) fun s₄ h₄ => ?_)
  · exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, fun _ => rfl, fun h' => by simp at h; omega⟩
  · have hjn : j + 1 < n := by simp at h; omega
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := encChain_ok hL d6 d7 s₃ base₃ data₃
      (fun w hw => by rw [rd₃', wr₃', ← hi.rd, ← hi.wr]; exact inRd (inT w hw)) (fun o ho => inN o ho hjn)
    exact WP.of_runBlock ⟨s₄, e₄, g₄, rd₄, wr₄, fun h' => by omega, fun _ => m₄⟩
  obtain ⟨g₄, rd₄, wr₄, mDone, mMore⟩ := h₄
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₄ c.dataReg c.dataReg (v := 16) (by decide)
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  have keep₆ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ c.dataReg → s₆.gpr x = s₃.gpr x := fun x h1 h2 h3 => by
    rw [o₆ x h3, g₄ x h1 h2]
  have left₆ : s₆.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by rw [keep₆ _ l6 l7 (Ne.symm hdl), left₃]
  have hz : isa.eval (.nonzero .x c.leftReg) s₆ = some !(decide (j + 1 = n)) := by
    rw [eval_nonzero, left₆, ofNat_beq_zero (by omega)]
    congr 2
    exact decide_eq_decide.mpr (by omega)
  have mem₆ : s₆.mem = s₄.mem := m₆
  have base₆ : s₆.gpr sb = B := by rw [keep₆ _ (by decide) (by decide) (Ne.symm dsb), base₃]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₄, rd₃']
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₄, wr₃']
  -- Block `j` is its ciphertext; block `j + 1`, if any, its plaintext XORed with it.
  have hlen : ∀ t, (cbcEncC ciph m₀ D iv t).length = 16 := fun t => by cases t <;> exact cs.cipher_len k _
  by_cases hdone : j + 1 = n
  · have hm : s₆.mem = s₃.mem := by rw [mem₆, mDone hdone]
    refine .inl ⟨by rw [hz, decide_eq_true hdone]; rfl, base₆, by rw [hm]; exact saved₃, fun i hin => ?_,
      by rw [hm]; exact fr₃, rd₆', wr₆'⟩
    rw [hm, ite_eq_left hin]
    by_cases h1 : i < 16 * j
    · rw [outA i (.inl h1) (by omega), hi.data i (by omega), encByte, ite_eq_left h1]
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 16 * j) := by
        rw [addr_add, show 16 * j + (i - 16 * j) = i by omega]
      rw [e1, A₃ _ (by omega), show i / 16 = j by omega, show i - 16 * j = i % 16 by omega]
  · have hjn : j + 1 < n := by omega
    have hm : s₆.mem = xor16 s₃.mem (A + BitVec.ofNat 64 16) T := by rw [mem₆, mMore hjn]
    have A16 : A + BitVec.ofNat 64 16 = D + BitVec.ofNat 64 (16 * (j + 1)) := by
      rw [addr_add, show 16 * j + 16 = 16 * (j + 1) by omega]
    have subN : Region.Sub ⟨A + BitVec.ofNat 64 16, 16⟩ ⟨D, 16 * n⟩ := by
      rw [A16]; exact VG.Offset.sub_base D (by omega)
    have dNT : Region.Disjoint ⟨A + BitVec.ofNat 64 16, 16⟩ ⟨T, 16⟩ := (dDS subT).sub_left subN
    have fN : Frame [⟨A + BitVec.ofNat 64 16, 16⟩] s₃.mem s₆.mem := by rw [hm]; exact two_frame
    refine .inr ⟨by rw [hz, decide_eq_false hdone]; rfl, base₆, ?_, fun i hi6 => ?_, ?_, left₆, hjn,
      fun i hin => ?_, ?_, rd₆', wr₆'⟩
    · exact cs.ready_frame ready₃ fN (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inl ((dDS subCore).sub_left subN).symm)
        fun r hr => by
          obtain ⟨h1, h2, -⟩ := of_not_modeRegs hr
          obtain ⟨h6, h7, -⟩ := not_own h1
          exact keep₆ r h6 h7 h2
    · rw [← saved₃ i hi6]
      exact fN.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (slotOut i hi6).2.2 subN) (by decide)
    · rw [a₆, g₄ _ d6 d7, data₃, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [hm]
      have hTA : ∀ u < 16, s₃.mem (T + BitVec.ofNat 64 u) = (cbcEncC ciph m₀ D iv j).getD u 0 := fun u hu => by
        rw [f₃ _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact fun h => dAT _ h (by simp only [Region.Contains]; rw [off_self T (by omega)]; omega)), C₂ u hu]
      by_cases h1 : 16 * (j + 1) ≤ i ∧ i < 16 * (j + 2)
      · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 16 + BitVec.ofNat 64 (i - 16 * (j + 1)) := by
          rw [A16, addr_add, show 16 * (j + 1) + (i - 16 * (j + 1)) = i by omega]
        have hu : i - 16 * (j + 1) < 16 := by omega
        rw [e1, xor16_in s₃.mem dNT hu, ← e1, outA i (.inr h1.1) hin, hi.data i hin, hTA _ hu, encByte,
          ite_eq_right (by omega), ite_eq_right (by omega), encByte, ite_eq_right (by omega),
          ite_eq_left (by omega), cbcEncPrev, ite_eq_right (by omega), Nat.add_sub_cancel]
      · have hout : ¬ (D + BitVec.ofNat 64 i - (A + BitVec.ofNat 64 16)).toNat < 16 := by
          rw [A16]; exact off_sub_not D (by omega) (by omega) (by decide) (by omega)
        rw [show xor16 s₃.mem (A + BitVec.ofNat 64 16) T (D + BitVec.ofNat 64 i) = s₃.mem (D + BitVec.ofNat 64 i)
          from two_out hout]
        by_cases h2 : 16 * j ≤ i ∧ i < 16 * (j + 1)
        · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 16 * j) := by
            rw [addr_add, show 16 * j + (i - 16 * j) = i by omega]
          rw [e1, A₃ _ (by omega), encByte, ite_eq_left (by omega), show i / 16 = j by omega,
            show i % 16 = i - 16 * j by omega]
        · rw [outA i (by omega) hin, hi.data i hin, encByte, encByte]
          by_cases h3 : i < 16 * j
          · rw [ite_eq_left h3, ite_eq_left (by omega)]
          · rw [ite_eq_right h3, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · exact fr₃.trans (fN.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subN⟩)

/-- The data loop. -/
theorem cbcEncLoop_wp (cs : CoreSpec c) {s₀ : State} {m₀ : Mem} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 16) (hp : GPre c s₀ B D n) {s : State}
    (hi : EInv cs s₀ m₀ B D n k iv 0 s) :
    WP isa (.loop c.cbcEncBlock (.nonzero .x c.leftReg)) s (EDone cs s₀ m₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ EInv cs s₀ m₀ B D n k iv j s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (cbcEncBlock_wp cs hiv hp hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - (j + 1), by have := d.lt; have := hj.lt; omega, j + 1, rfl, d⟩

end VG.Proof.Modes.AArch64
