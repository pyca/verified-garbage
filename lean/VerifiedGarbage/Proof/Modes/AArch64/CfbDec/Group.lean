module

import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Gather
import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Pure
public import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Modes.AArch64.CfbDec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Modes.Cbc
public import VerifiedGarbage.Proof.Modes.Fb

/-! # One batch and the data loop of CFB128 decryption -/
@[expose] public section
namespace VG.Proof.Modes.AArch64.CfbDec
open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Spec.Aes (bytesAt)
variable {c : Core}
/-- The data loop, before group `g`, from the IV `iv` with the key `k`. -/
structure Inv (cs : BlockSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte) (g : Nat)
    (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (c.G * g))
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - c.G * g)
  lt : c.G * g < n
  chain : ∀ u < 8 * c.bw, s.mem (chainAddr c B + BitVec.ofNat 64 u) =
    (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g)).getD u 0
  data : DInv (8 * c.bw) s₀.mem s.mem D n (c.G * g) (fbOut .cfbDec (8 * c.bw) (cs.cipher k) s₀.mem D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure Done (cs : BlockSpec c) (s₀ : State) (B D : Addr) (n : Nat) (k : cs.Key) (iv : List Byte) (s : State) :
    Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  data : DInv (8 * c.bw) s₀.mem s.mem D n n (fbOut .cfbDec (8 * c.bw) (cs.cipher k) s₀.mem D iv)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem group_wp (cs : BlockSpec c) (hbw : c.bw = 2) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {iv : List Byte}
    (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {g : Nat} {s : State}
    (hi : Inv cs s₀ B D n k iv g s) :
    WP isa c.cfbDecGroup s fun s' =>
      (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ Done cs s₀ B D n k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ Inv cs s₀ B D n k iv (g + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  have hL0 : 0 < 8 * c.bw := by omega_using [hbw0]
  have hGb : c.G ≤ c.bw * c.G := Nat.le_mul_of_pos_left _ hbw0
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨-, -, d8, -, -, d13, d14, -, d16, -⟩ := not_own down
  obtain ⟨-, -, -, -, -, l13, -, -, -, -⟩ := not_own lown
  have hN : 8 * c.total < 2 ^ 64 := by omega_using [hsm]
  let v := n - c.G * g
  let cc := min v c.G
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega_using [hL0])
  have hv : v < 2 ^ 64 := by omega_using [hfitD, h8n]
  have hc0 : 0 < cc := by omega_using [hG0, hk]
  have hcG : cc ≤ c.G := by omega_using []
  have hccsmall : cc < 2^16 := Nat.lt_of_le_of_lt hcG hL.G_lt
  have hkc : 8 * c.bw * (c.G * g) + 8 * c.bw * cc ≤ 8 * c.bw * n := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega_using [hc0])
  have hbwcc : 8 * c.bw * cc = 8 * (c.bw * cc) := Nat.mul_assoc _ _ _
  have hbG : c.bw * cc ≤ c.bw * c.G := Nat.mul_le_mul_left _ hcG
  have hcc1 : 8 * c.bw ≤ 8 * c.bw * cc := Nat.le_mul_of_pos_right _ hc0
  let A := D + BitVec.ofNat 64 (8 * c.bw * (c.G * g))
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  let H := chainAddr c B
  have hwS : (⟨B, 8 * c.total⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subS : ∀ {d l : Nat}, d + l ≤ 8 * c.total → Region.Sub ⟨B + BitVec.ofNat 64 d, l⟩ ⟨B, 8 * c.total⟩ :=
    fun h => VG.Offset.sub_base B h
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ :=
    Region.sub_prefix (by omega_using [hroom])
  have subA : Region.Sub ⟨A, 8 * c.bw * cc⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hkc
  have subT : Region.Sub ⟨T, 8 * c.bw * cc⟩ ⟨B, 8 * c.total⟩ := subS (by omega_using [hroom, hbuf, hbwcc, hbG])
  have subH : Region.Sub ⟨H, 8 * c.bw⟩ ⟨B, 8 * c.total⟩ :=
    subS (by simp only [Core.hiSlot]; omega_using [hroom, hbw2])
  have subTbuf : Region.Sub ⟨T, 8 * c.bw * cc⟩ (blkRegion c B) := Region.sub_prefix (Nat.mul_le_mul_left _ hcG)
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.total⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  have dAT : Region.Disjoint ⟨A, 8 * c.bw * cc⟩ ⟨T, 8 * c.bw * cc⟩ := (dDS subT).sub_left subA
  have dTH : Region.Disjoint ⟨T, 8 * c.bw * cc⟩ ⟨H, 8 * c.bw⟩ :=
    VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega_using [hbuf, hbwcc, hbG])) (by omega_using [hroom, hbuf, hN, hbwcc, hbG]) (by simp only [Core.hiSlot]; omega_using [hroom, hbw2, hN])
  have dAH : Region.Disjoint ⟨A, 8 * c.bw * cc⟩ ⟨H, 8 * c.bw⟩ := (dDS subH).sub_left subA
  have dHcore : Region.Disjoint ⟨H, 8 * c.bw⟩ (coreRegion c B) :=
    VG.Offset.disjoint_base B (by simp only [Core.hiSlot]; omega_using []) (by simp only [Core.hiSlot]; omega_using [hroom, hbw2, hN])
  have inT : ∀ t, t < c.bw * cc → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by omega_using [hroom, hbuf, hbG, ht]) (by omega_using [hroom, hbuf, hN, hbG, ht])⟩
  have inA : ∀ t, t < c.bw * cc → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := fun t ht =>
    ⟨_, hwD, by rw [addr_add]; exact VG.Offset.contains_base D (by omega_using [hkc, hbwcc, ht]) (by omega_using [hfitD, hkc, hbwcc, ht])⟩
  have inH : ∀ w < c.bw, InRegions s.wr (H + BitVec.ofNat 64 (8 * w)) 8 := fun w hw =>
    ⟨_, hwS, by
      rw [addr_add]
      exact VG.Offset.contains_base B (by simp only [Core.hiSlot]; omega_using [hroom, hbw2, hw])
        (by simp only [Core.hiSlot]; omega_using [hroom, hbw2, hN, hw])⟩
  unfold Core.cfbDecGroup
  -- Gather the previous original ciphertexts before any plaintext store.
  refine WP.seq (WP.mono_syms (groupCount_wp hL.lgG_lt l13 hi.leftR hv) fun s₁ ⟨c₁,o₁,m₁,rd₁,wr₁⟩ sy₁ => ?_)
  have base₁ : s₁.gpr sb = B := by rw [o₁ _ (by decide) (by decide),hi.base]
  refine WP.seq (WP.mono_syms (gather_wp hbw hc0 (by omega_using [hccsmall])
    hL.bufImm (by simp only [Core.hiSlot]; omega_using [hsm,hroom]) d8 d14 base₁
    (by rw [o₁ _ d13 d16,hi.dataR]) c₁
    (fun w hw => by rw [wr₁]; exact inT w (by rw [hbw]; exact hw))
    (fun w hw => by rw [wr₁]; exact inH w (by rw [hbw]; exact hw))
    (fun w hw => by rw [rd₁,wr₁]; exact inRd (inA w (by rw [hbw]; exact hw)))
    (by simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul] using dAT.symm) (by simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul] using dTH)
    (by simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul] using dAH.symm)) fun s₃ h₃ sy₃ => ?_)
  have keep₃ : ∀ r, r ∉ ownRegs → s₃.gpr r = s.gpr r := fun r hr => by
    obtain ⟨-, -, h8, -, -, h13, h14, h15, h16, h17⟩ := not_own hr
    rw [h₃.regs r h8 h14 h15 h17,o₁ r h13 h16]
  have base₃ : s₃.gpr sb = B := by rw [keep₃ _ (by decide),hi.base]
  have rd₃' : s₃.rd = s.rd := by rw [h₃.rd,rd₁]
  have wr₃' : s₃.wr = s.wr := by rw [h₃.wr,wr₁]
  have f₃ : Frame [⟨T,8*c.bw*cc⟩,⟨H,8*c.bw⟩] s.mem s₃.mem := by
    simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul,m₁] using h₃.frame
  have ready₃ : cs.Ready s₃ B k := cs.ready_frame hi.ready f₃ (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr subTbuf
    · exact .inl dHcore.symm)
    ⟨fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_,hwS,subT⟩
      · exact ⟨_,hwS,subH⟩,
      rd₃',wr₃',by rw [sy₃,sy₁]⟩ fun r hr => keep₃ r (of_not_modeRegs hr).1
  -- Encrypt the gathered inputs.
  refine WP.seq (WP.mono (cs.crypt_wp base₃ ⟨by rw [wr₃']; exact hwS, hfit⟩ ready₃)
    fun s₄ ⟨base₄, dr₄, lr₄, ready₄, f₄, ks₄, rd₄, wr₄⟩ => ?_)
  have left₄ : s₄.gpr c.leftReg = BitVec.ofNat 64 v := by rw [lr₄, keep₃ _ lown, hi.leftR]
  have data₄ : s₄.gpr c.dataReg = A := by rw [dr₄, keep₃ _ down, hi.dataR]
  refine WP.seq (WP.mono_syms (groupCount_wp hL.lgG_lt l13 left₄ hv) fun s₅ ⟨c₅, o₅, m₅, rd₅, wr₅⟩ sy₅ => ?_)
  have base₅ : s₅.gpr sb = B := by rw [o₅ _ (by decide) (by decide), base₄]
  obtain ⟨s₆, e₆, a₆, b₆, t₆, o₆, m₆, rd₆, wr₆⟩ := xorArgs_ok hL.bufImm d14 s₅ base₅
  refine WP.seq (WP.of_runBlock ⟨s₆, e₆, ?_⟩)
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃']
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃']
  have base₆ : s₆.gpr sb = B := by rw [o₆ _ (by decide) (by decide) (by decide), base₅]
  -- XOR encrypted gathered inputs into the original ciphertexts.
  refine WP.seq (WP.mono_syms (xorBlocks_wp (A:=T) (B:=A) hc0 (by omega_using [hccsmall])
    (fun w hw => by rw [rd₆',wr₆']; exact inRd (inT w (by rw [hbw]; exact hw)))
    (fun w hw => by rw [wr₆']; exact inA w (by rw [hbw]; exact hw))
    (by simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul] using dAT.symm)
    ⟨by simpa only [Nat.mul_zero,BitVec.add_zero] using a₆,by rw [b₆,o₅ _ d13 d16,data₄]; simp,
      by rw [t₆,c₅,Nat.sub_zero],fun t ht => by omega,
      fun _ _ _ => rfl,Frame.refl _ _,fun _ _ _ _ _ _ => rfl,rfl,rfl⟩)
    fun s₇ h₇ sy₇ => ?_)
  have x15₇ : s₇.gpr .x15 = A + BitVec.ofNat 64 (8*c.bw*cc) := by simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul] using h₇.x15
  have f₇ : Frame [⟨A,8*c.bw*cc⟩] s₄.mem s₇.mem := by
    rw [hbw,← mem₆]; exact h₇.frame
  have g₇ : ∀ r, r ∉ ownRegs → s₇.gpr r = s₄.gpr r := fun r hr => by
    obtain ⟨-, -, h8, h9, -, h13, h14, h15, h16, h17⟩ := not_own hr
    rw [h₇.regs r h8 h9 h14 h15 h17, o₆ r h14 h15 h17, o₅ r h13 h16]
  have left₇ : s₇.gpr c.leftReg = BitVec.ofNat 64 v := by rw [g₇ _ lown, left₄]
  have x16₇ : s₇.gpr .x16 = BitVec.ofNat 64 cc := by
    rw [h₇.regs _ (by decide) (by decide) (by decide) (by decide) (by decide), o₆ _ (by decide) (by decide)
      (by decide), c₅]
  -- On to the next group.
  obtain ⟨s₈, e₈, d₈, l₈, o₈, m₈, rd₈, wr₈⟩ := advance_ok hdl d16 s₇
  refine WP.of_runBlock ⟨s₈, e₈, ?_⟩
  have left₈ : s₈.gpr c.leftReg = BitVec.ofNat 64 (v - cc) := by
    rw [l₈, left₇, x16₇, VG.Offset.ofNat_sub_ofNat (by omega_using [])]
  have hz : isa.eval (.nonzero .x c.leftReg) s₈ = some !(decide (v = cc)) := by
    rw [eval_nonzero, left₈, ofNat_beq_zero (by omega_using [hv]), decide_eq_decide.mpr (show v - cc = 0 ↔ v = cc by omega_using [])]
  have keep₈ : ∀ r, r ∉ modeRegs c → s₈.gpr r = s₄.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
    rw [o₈ r h2 h3, g₇ r h1]
  have ready₈ : cs.Ready s₈ B k := by
    refine cs.ready_frame ready₄ (by rw [m₈]; exact f₇) (fun r hr => ?_) ⟨fun r hr => ?_,?_,?_,?_⟩ keep₈
    · simp only [List.mem_singleton] at hr; subst hr
      exact .inl (((dDS subCore).sub_left subA).symm)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_,by rw [wr₄,wr₃']; exact hwD,subA⟩
    · rw [rd₈,h₇.rd,rd₆',rd₄,rd₃']
    · rw [wr₈,h₇.wr,wr₆',wr₄,wr₃']
    · rw [runBlock_syms e₈,sy₇,runBlock_syms e₆,sy₅]
  -- The bytes, through the steps.
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega_using [hfitD]
  have outCore : ∀ {R : Region}, Region.Disjoint R (coreRegion c B) → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₄.mem (R.base + BitVec.ofNat 64 i) = s₃.mem (R.base + BitVec.ofNat 64 i) := fun hd hl i hi =>
    f₄.bytes (R := _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hl hi
  have outT : ∀ {R : Region}, Region.Disjoint R ⟨T, 8 * c.bw * cc⟩ → Region.Disjoint R ⟨H,8*c.bw⟩ → R.len ≤ 2 ^ 64 →
      ∀ i < R.len, s₃.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) := fun hd hh hl i hi =>
    f₃.bytes (R := _) (fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hd
      · exact hh) hl hi
  -- The data before the XOR: as on entry.
  have dat₄ : ∀ i < 8 * c.bw * n, s₄.mem (D + BitVec.ofNat 64 i) = s.mem (D + BitVec.ofNat 64 i) := fun i hin => by
    rw [outCore (R := ⟨D, 8 * c.bw * n⟩) (dDS subCore) hn64 i hin,
      outT (R := ⟨D, 8 * c.bw * n⟩) (dDS subT) (dDS subH) hn64 i hin]
  have dat0 : ∀ i, 8 * c.bw * (c.G * g) ≤ i → i < 8 * c.bw * n →
      s.mem (D + BitVec.ofNat 64 i) = s₀.mem (D + BitVec.ofNat 64 i) :=
    fun i h1 h2 => by rw [hi.data i h2, ite_eq_right (by omega_using [h1])]
  -- Each gathered block is the preceding original ciphertext (or IV).
  have dec₄ : ∀ j < cc, ∀ u < 8*c.bw, s₄.mem (T+BitVec.ofNat 64 (8*c.bw*j+u)) =
      (cs.cipher k (cbcPrev (8*c.bw) s₀.mem D iv (c.G*g+j))).getD u 0 := by
    intro j hj u hu
    have eT : T+BitVec.ofNat 64 (8*c.bw*j+u) = blkAddr c B j+BitVec.ofNat 64 u := by
      simp only [T,blkAddr]; rw [addr_add,addr_add,Nat.add_assoc]
    rw [eT,← bytesAt_getD s₄.mem _ hu,ks₄ _ (by omega_using [hj])]
    congr 2
    apply List.ext_getElem (by rw [cbcPrev]; split <;> simp [bytesAt,hiv])
    intro x h1 h2
    rw [show (cbcPrev (8*c.bw) s₀.mem D iv (c.G*g+j))[x] =
      (cbcPrev (8*c.bw) s₀.mem D iv (c.G*g+j)).getD x 0 from List.getElem_eq_getD 0]
    have hx : x < 8*c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt,List.getElem_map,List.getElem_range,blkAddr]
    rw [addr_add,show 8*c.buf+8*c.bw*j+x=8*c.buf+(8*c.bw*j+x) by omega,← addr_add]
    have inp := h₃.inputs (8*c.bw*j+x) (by rw [hbw] at *; have := idx_lt (L:=16) hj; omega)
    -- Replace the fixed byte length only after obtaining the gather equality.
    have inp' : s₃.mem (T+BitVec.ofNat 64 (8*c.bw*j+x)) =
        if 8*c.bw*j+x < 8*c.bw then s.mem (H+BitVec.ofNat 64 (8*c.bw*j+x))
        else s.mem (A+BitVec.ofNat 64 (8*c.bw*j+x-8*c.bw)) := by
      simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul,m₁] using inp
    rw [inp']
    by_cases hj0 : j=0
    · subst j
      rw [Nat.mul_zero,Nat.zero_add,ite_eq_left hx,hi.chain x hx,Nat.add_zero]
    · have hjp : 0<j := Nat.pos_of_ne_zero hj0
      have hmul := Nat.le_mul_of_pos_right (8*c.bw) hjp
      rw [ite_eq_right (by omega_using [hmul]),addr_add,
        dat0 _ (by omega_using [hmul]) (by have := idx_lt (L:=8*c.bw) hj; omega_using [hkc,this,hx]),
        cbcPrev,ite_eq_right (by omega_using [hj0])]
      rw [bytesAt_getD _ _ hx,addr_add]
      congr 1
      congr 1
      congr 1
      have := Nat.mul_sub_one (8*c.bw) j
      have := Nat.mul_sub_one (8*c.bw) (c.G*g+j)
      have := Nat.mul_add (8*c.bw) (c.G*g) j
      omega
  -- Offsets within the data.
  have eA : ∀ t, D + BitVec.ofNat 64 (8 * c.bw * (c.G * g) + t) = A + BitVec.ofNat 64 t := fun t => by
    rw [← addr_add]
  have prevEq : ∀ {j u : Nat}, 0 < j → 8 * c.bw * (c.G * g) + (8 * c.bw * (j - 1) + u) =
      8 * c.bw * (c.G * g + j - 1) + u := fun {j u} hj => by
    have := Nat.mul_sub_one (8 * c.bw) j
    have := Nat.mul_sub_one (8 * c.bw) (c.G * g + j)
    have := Nat.mul_add (8 * c.bw) (c.G * g) j
    have := Nat.le_mul_of_pos_right (8 * c.bw) hj
    omega_arith
  have hdata : DInv (8 * c.bw) s₀.mem s₈.mem D n (c.G * g + cc) (fbOut .cfbDec (8 * c.bw) (cs.cipher k) s₀.mem D iv) := by
    refine dinv_of_blocks hL0 fun q hq r hr => ?_
    rw [m₈]
    have hqn := idx_lt (L := 8 * c.bw) hq
    by_cases hin : c.G * g ≤ q ∧ q < c.G * g + cc
    · obtain ⟨j, rfl⟩ : ∃ j, q = c.G * g + j := ⟨q - c.G * g, by omega_using [hin]⟩
      have hjc : j < cc := by omega_using [hin]
      have hjl := idx_lt (L := 8 * c.bw) hjc
      have xx := h₇.xored (8*c.bw*j+r) (by rw [hbw] at *; omega_using [hjl,hr])
      have xx' : s₇.mem (A+BitVec.ofNat 64 (8*c.bw*j+r)) =
          s₆.mem (T+BitVec.ofNat 64 (8*c.bw*j+r)) ^^^ s₆.mem (A+BitVec.ofNat 64 (8*c.bw*j+r)) := xx
      rw [Nat.mul_add,Nat.add_assoc,eA,xx',mem₆,dec₄ j hjc r hr,← eA,
        dat₄ _ (by omega_using [hr,hjl,hkc]),dat0 _ (by omega_using []) (by omega_using [hr,hjl,hkc]),
        ite_eq_left hin.2,fbOut_getD .cfbDec (cs.cipher_len k) _ _ _ _ hr,input_eq,BitVec.xor_comm]
      rw [Nat.mul_add,Nat.add_assoc]
    · have hlo : q < c.G * g → 8 * c.bw * q + r < 8 * c.bw * (c.G * g) := fun h => by
        have := idx_lt (L := 8 * c.bw) h; omega_using [hr, this]
      have hhi : c.G * g + cc ≤ q → 8 * c.bw * (c.G * g) + 8 * c.bw * cc ≤ 8 * c.bw * q := fun h => by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h
      have hout : ∀ R ∈ [(⟨A,8*c.bw*cc⟩ : Region)],
          ¬ R.Contains (D+BitVec.ofNat 64 (8*c.bw*q+r)) 1 := fun R hR => by
        simp only [List.mem_singleton] at hR; subst hR
        exact not_contains_off D (by omega_using [hin,hlo,hhi]) (by omega_using [hn64,hr,hqn])
          (by omega_using [hcc1,hr]) (by omega_using [hkc,hn64])
      rw [f₇ _ hout, dat₄ _ (by omega_using [hr, hqn]), hi.data _ (by omega_using [hr, hqn]), idx_div hr, idx_mod hr]
      by_cases h2 : q < c.G * g
      · rw [ite_eq_left (hlo h2), ite_eq_left (by omega_using [h2])]
      · rw [ite_eq_right (by have := Nat.mul_le_mul_left (8 * c.bw) (Nat.le_of_not_lt h2); omega_using [this]),
          ite_eq_right (by omega_using [hin, h2])]
  -- The chaining value: the group's last ciphertext block.
  have chain₈ : ∀ u < 8 * c.bw, s₈.mem (H + BitVec.ofNat 64 u) =
      (cbcPrev (8 * c.bw) s₀.mem D iv (c.G * g + cc)).getD u 0 := by
    intro u hu
    have hl := idx_lt (L := 8 * c.bw) (show cc - 1 < cc by omega_using [hc0])
    have ch₃ : s₃.mem (H+BitVec.ofNat 64 u) = s.mem (A+BitVec.ofNat 64 (8*c.bw*(cc-1)+u)) := by
      simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul,m₁] using h₃.chain u (by simpa only [A,T,H,chainAddr,hbw,Nat.reduceMul] using hu)
    rw [m₈,f₇.bytes (R:=⟨H,8*c.bw⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAH.symm)
      (by simp only; omega_using [hbw2]) hu,
      outCore (R:=⟨H,8*c.bw⟩) dHcore (by simp only; omega_using [hbw2]) u hu,
      ch₃,← eA,dat0 _ (by omega_using []) (by omega_using [hkc,hu,hl]),
      cbcPrev,ite_eq_right (by omega_using [hc0]),bytesAt_getD _ _ hu,addr_add,prevEq hc0]
  -- The slots.
  have wS : ∀ j, c.slots ≤ j → j < c.slots + 10 → ∀ r ∈ [(⟨T, 8 * c.bw * cc⟩ : Region), ⟨A, 8 * c.bw * cc⟩,
      ⟨H, 8 * c.bw⟩], Region.Disjoint ⟨wordAddr B j, 8⟩ r := fun j h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint B (.inr (by omega_using [hbuf, hbwcc, hbG, h1])) (by omega_using [hroom, hN, h2]) (by omega_using [hroom, hbuf, hN, hbwcc, hbG])
    · exact (((dDS (subS (show 8 * j + 8 ≤ 8 * c.total by omega_using [hroom, h2]))).sub_left
        subA).symm)
    · exact VG.Offset.disjoint B (.inl (by simp only [Core.hiSlot]; omega_using [h2])) (by omega_using [hroom, hN, h2])
        (by simp only [Core.hiSlot]; omega_using [hroom, hbw2, hN])
  have saved₈ : ∀ i < 10, s₈.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [m₈, ← hi.saved i hi10]
    refine (f₇.readW (Region.contains_self _ _) (fun r hr => wS _ (by omega_using []) (by omega_using [hi10]) r (by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self)) (by decide)).trans ?_
    refine (f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base B (by omega_using []) (by omega_using [hroom, hN, hi10])) (by decide)).trans ?_
    exact f₃.readW (Region.contains_self _ _) (fun r hr => wS _ (by omega) (by omega_using [hi10]) r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) (by decide)
  have fr : Frame [⟨B,8*c.total⟩,⟨D,8*c.bw*n⟩] s₀.mem s₈.mem := by
    rw [m₈]
    refine hi.frame.trans (((f₃.sub fun r hr => ⟨⟨B,8*c.total⟩,List.mem_cons_self,by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact subT
      · exact subH⟩).trans
      (f₄.sub fun r hr => ⟨⟨B,8*c.total⟩,List.mem_cons_self,by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans
      (f₇.sub fun r hr => ⟨⟨D,8*c.bw*n⟩,List.mem_cons_of_mem _ List.mem_cons_self,by
        simp only [List.mem_singleton] at hr; subst hr; exact subA⟩))
  have base₈ : s₈.gpr sb = B := by rw [o₈ _ (Ne.symm dsb) (Ne.symm lsb), g₇ _ (by decide), base₄]
  have rd₈' : s₈.rd = s₀.rd := by rw [rd₈, h₇.rd, rd₆', hi.rd]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, h₇.wr, wr₆', hi.wr]
  by_cases hdone : v = cc
  · refine .inl ⟨by rw [hz, decide_eq_true hdone]; rfl, base₈, saved₈, ?_, fr, rd₈', wr₈'⟩
    rw [show n = c.G * g + cc by omega_using [hc0, hdone]] at hdata ⊢
    exact hdata
  · have hcc : cc = c.G := by omega_using [hdone]
    have hg1 : c.G * (g + 1) = c.G * g + cc := by rw [hcc, Nat.mul_succ]
    refine .inr ⟨by rw [hz, decide_eq_false hdone]; rfl, base₈, ready₈, saved₈, ?_, ?_, by omega_using [hdone, hg1], ?_,
      by rw [hg1]; exact hdata, fr, rd₈', wr₈'⟩
    · rw [d₈, x15₇, addr_add, hg1, Nat.mul_add]
    · rw [left₈, hg1]; congr 1; omega_using []
    · rw [hg1]; exact chain₈

/-- The data loop. -/
theorem loop_wp (cs : BlockSpec c) (hbw : c.bw = 2) {s₀ : State} {B D : Addr} {n : Nat} {k : cs.Key} {iv : List Byte}
    (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) {s : State} (hi : Inv cs s₀ B D n k iv 0 s) :
    WP isa (.loop c.cfbDecGroup (.nonzero .x c.leftReg)) s (Done cs s₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ g, m = n - c.G * g ∧ Inv cs s₀ B D n k iv g s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hg⟩ := hs
  refine WP.mono (group_wp cs hbw hiv hp hg) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · have hG := cs.layout.G_pos
    exact .inr ⟨z, n - c.G * (g + 1),
      by have := d.lt; have := hg.lt; rw [Nat.mul_succ] at *; omega_arith, g + 1, rfl, d⟩

end VG.Proof.Modes.AArch64.CfbDec
