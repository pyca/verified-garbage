import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Dec
import VerifiedGarbage.Proof.Aes.AArch64.Blocks

/-!
# AES on whole blocks with the Armv8 Cryptographic Extension

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.AArch64.Aese.encryptBlocks` and `decryptBlocks` against
`Proof.Aes.blocksAArch64` (the contract the bitsliced functions are proven
against), and so against the shared contracts.

Both are `blocks` around a transformation of the block registers: `aes`
(`aes_ok`) or `aesDec` (`aesDec_ok`), which needs the round keys as its
setup leaves them (`Keys` or `DKeys`): a `BlockFn`. The loops keep, after `c`
blocks, the first `c` data blocks transformed and the others as they were
(`EcbInv`, as for the bitsliced functions): each group is loaded into the
registers (`ldData_ok`), transformed, and stored back (`stData_ok`).
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG VG.AArch64
open VG.Impl.Aes.AArch64.Aese
open VG.Proof.Aes.AArch64 (EcbInv ecbOut ecbInv_orig)
open VG.Spec.Aes (roundKey)

/-- A transformation of the block registers, `F nr w` of each, given what
`K nr w` says of the state, which survives the transformation and anything
that leaves `v16`–`v30`, `x6` and `x7` alone. -/
structure BlockFn where
  f : List VReg → Prog isa
  F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State
  K : Nat → List Byte → State → Prop
  of_v : ∀ {nr w} {vs : List VReg} {s s' : State}, K nr w s → BlockRegs vs →
    (∀ r, r ∉ vs → s'.v r = s.v r) → s'.gpr .x6 = s.gpr .x6 → s'.gpr .x7 = s.gpr .x7 → K nr w s'
  ok : ∀ {regs : List VReg} {nr w} {s : State}, BlockRegs regs → K nr w s →
    WP isa (f regs) s fun s' => (∀ b ∈ regs, st (s'.v b) = F nr w (st (s.v b))) ∧ VFrame regs s s'

theorem DKeys.of_v {nr : Nat} {w : List Byte} {vs : List VReg} {s s' : State} (h : DKeys nr w s)
    (hrs : BlockRegs vs) (hv : ∀ r, r ∉ vs → s'.v r = s.v r) (h6 : s'.gpr .x6 = s.gpr .x6)
    (h7 : s'.gpr .x7 = s.gpr .x7) : DKeys nr w s' :=
  ⟨h.rounds, by rw [hv _ hrs.v30]; exact h.last,
    fun j h1 h2 => by rw [hv _ (hrs.dreg j)]; exact h.mid j h1 h2,
    by rw [hv _ hrs.v16]; exact h.k0, by rw [h6]; exact h.x6, by rw [h7]; exact h.x7⟩

def encFn : BlockFn :=
  ⟨aes, Spec.Aes.cipher, Keys, fun h hrs hv h6 h7 => h.of_v hrs hv h6 h7, fun hr hK => aes_ok hr hK⟩

def decFn : BlockFn :=
  ⟨aesDec, Spec.Aes.invCipher, DKeys, fun h hrs hv h6 h7 => h.of_v hrs hv h6 h7,
    fun hr hK => aesDec_ok hr hK⟩

/-! ## The precondition and the loop invariant -/

section
variable (s₀ : State)

abbrev bkp : Addr := s₀.gpr .x0
abbrev bnr : Nat := (s₀.gpr .x1).toNat
abbrev bdp : Addr := s₀.gpr .x2
abbrev bnb : Nat := (s₀.gpr .x3).toNat
abbrev bdR : Region := ⟨bdp s₀, 16 * bnb s₀⟩
/-- The key schedule. -/
abbrev bsch : List Byte := Spec.Aes.bytesAt s₀.mem (bkp s₀) (16 * (bnr s₀ + 1))

end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨bkp s₀, 240⟩]
  wr : s₀.wr = [bdR s₀, ⟨s₀.gpr .x4, 2048⟩]
  s_d : Region.Disjoint ⟨bkp s₀, 240⟩ (bdR s₀)
  d_s : Region.Disjoint (bdR s₀) ⟨s₀.gpr .x4, 2048⟩
  wrap : (bdp s₀).toNat + 16 * bnb s₀ ≤ 2 ^ 64
  rounds : bnr s₀ = 10 ∨ bnr s₀ = 12 ∨ bnr s₀ = 14

theorem bpre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State}
    (h : (Proof.Aes.blocksAArch64 f).pre s₀) : BPre s₀ := by
  obtain ⟨h1, h2, h3, _, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h5, h6, h7⟩

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem nb16 : 16 * bnb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega

theorem dat : bdR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem n16 : 16 * bnb s₀ < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hc => hp.d_s (s₀.gpr .x4) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (s₀.gpr .x4 - bdp s₀).isLt
  omega

theorem key_in {o : Nat} (h : o + 16 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (bkp s₀ + BitVec.ofNat 64 o) 16 :=
  ⟨⟨bkp s₀, 240⟩, by rw [hp.rd]; simp, Offset.contains_base _ h (by omega)⟩

end BPre

/-- After `c` blocks, with the data pointer and count at block `p`. -/
structure BInv (B : BlockFn) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ bnb s₀
  keys : B.K (bnr s₀) (bsch s₀) s
  x2 : s.gpr .x2 = bdp s₀ + BitVec.ofNat 64 (16 * p)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (bnb s₀ - p)
  frame : Frame [bdR s₀] s₀.mem s.mem
  data : EcbInv s₀.mem s.mem (bdp s₀) (bnb s₀) c (ecbOut B.F s₀.mem (bdp s₀) (bnr s₀) (bsch s₀))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-! ## Loading and storing the blocks -/

theorem st_readW (m : Mem) (p : Addr) : st (m.readW p 128) = Spec.Aes.stateAt m p := by
  apply Vector.ext; intro i hi
  simp only [st, Spec.Aes.stateAt, Vector.getElem_ofFn]
  exact vbyte_readW m p hi

theorem ldData_ok : ∀ (regs : List VReg) (j : Nat) (s : State), regs.Nodup → j + regs.length ≤ 4096 →
    (∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * (j + k))) 16) →
    WP isa (.block (ldData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), s'.v regs[k] = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      Fr [] regs s s'
  | [], _, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Fr.refl _ _ _⟩
  | b :: bs, j, s, hnd, hj, hin => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hj
    rw [ldData, WP.block_cons_iff]
    refine ⟨_, exec_ldrq (by omega) (by simpa using hin 0 (by simp)), ?_⟩
    refine WP.mono (ldData_ok bs (j + 1) _ (List.nodup_cons.mp hnd).2 (by omega) fun k hk => by
      have := hin (k + 1) (by simp; omega)
      simpa [State.setV, show j + 1 + k = j + (k + 1) by omega] using this)
      fun s' ⟨e, f⟩ => ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => simp only [List.getElem_cons_zero, Nat.add_zero]; rw [f.v _ hbs, setV_v_self]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk)]
        simp [State.setV, show j + 1 + k = j + (k + 1) by omega]
    · exact ⟨fun r _ => by rw [f.gpr r (by simp)]; rfl, fun r hr => by
        simp only [List.mem_cons, not_or] at hr
        rw [f.v r hr.2, setV_v_of_ne _ _ hr.1], f.sp, f.mem, f.rd, f.wr⟩

theorem off_toNat' (D : Addr) {i k : Nat} (hi : i < 2 ^ 64) (hk : k < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 k)).toNat =
      if k ≤ i then i - k else 2 ^ 64 + i - k := Offset.sub_toNat' D hk hi

/-- One block stored, by a 16-byte store. -/
theorem ecbInv_write {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 128}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : EcbInv m₀ m D n k F)
    (hv : ∀ t < 16, vbyte v t = (F k).getD t 0) :
    EcbInv m₀ (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) D n (k + 1) F ∧
      Frame [⟨D, 16 * n⟩] m (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · show (if _ then _ else _) = _
    rw [off_toNat' D (by omega) (by omega)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (k + 1) by omega)]
        show vbyte _ _ = _
        rw [hv _ h2, show i / 16 = k by omega, show i % 16 = i - 16 * k by omega]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega), h i hi,
        ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    show (if _ then _ else _) = _
    rw [ite_eq_right]
    intro hlt
    apply hx'
    have := (x - D).isLt
    rw [Offset.sub_add_eq] at hlt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * k < 2 ^ 64 by omega)] at hlt
    omega

theorem stData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State} (hn : 16 * n ≤ 2 ^ 64) :
    ∀ (regs : List VReg) (j : Nat) (s : State),
    s.gpr .x2 = D + BitVec.ofNat 64 (16 * c) → j + regs.length ≤ 4096 → c + j + regs.length ≤ n →
    (⟨D, 16 * n⟩ : Region) ∈ s.wr → EcbInv m₀ s.mem D n (c + j) F →
    (∀ k (h : k < regs.length), ∀ t < 16, vbyte (s.v regs[k]) t = (F (c + j + k)).getD t 0) →
    WP isa (.block (stData regs j)) s fun s' =>
      EcbInv m₀ s'.mem D n (c + j + regs.length) F ∧ Frame [⟨D, 16 * n⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.v = s.v ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, hD, _ => WP.block_nil ⟨by simpa using hD, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩
  | b :: bs, j, s, hx2, hj, hc, hw, hD, hF => by
    simp only [List.length_cons] at hj hc
    have ha : s.gpr .x2 + BitVec.ofNat 64 (16 * j) = D + BitVec.ofNat 64 (16 * (c + j)) := by
      rw [hx2, Offset.add_add_eq D (show 16 * c + 16 * j = 16 * (c + j) by omega)]
    rw [stData, WP.block_cons_iff]
    refine ⟨_, exec_strq (by omega) (by rw [ha]; exact ⟨_, hw, Offset.contains_base D (by omega) (by omega)⟩), ?_⟩
    rw [ha]
    have hst := ecbInv_write hn (by omega) hD (v := s.v b) fun t ht => by
      have := hF 0 (by simp) t ht
      simpa using this
    refine WP.mono (stData_ok (m₀ := m₀) (c := c) (F := F) hn bs (j + 1) _ hx2 (by omega) (by omega) hw
      (by rw [show c + (j + 1) = c + j + 1 by omega]; exact hst.1) (fun k hk t ht => by
        have := hF (k + 1) (by simp; omega) t ht
        simp only [List.getElem_cons_succ] at this
        rw [show c + (j + 1) + k = c + j + (k + 1) by omega]; exact this))
      fun s' ⟨d', f', g', v', sp', rd', wr'⟩ => ⟨?_, hst.2.trans f', g', v', sp', rd', wr'⟩
    rw [List.length_cons, show c + j + (bs.length + 1) = c + (j + 1) + bs.length by omega]; exact d'

/-! ## The loop bodies -/

theorem bregs_ok (rs : List VReg) (h : rs = regs8 ∨ rs = [.v0]) : BlockRegs rs := by
  rcases h with rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- Load, transform and store the blocks `c … c + N − 1` (`N` the number of
registers). -/
theorem group_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) (rs : List VReg) (hrs : rs = regs8 ∨ rs = [.v0])
    (tail : List Instr) {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ c c s) (hQ : ∀ s', BInv B s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ldData rs 0)) (.seq (B.f rs) (.block (stData rs 0 ++ tail)))) s Q := by
  have hbr := bregs_ok rs hrs
  have hlen : rs.length ≤ 8 := by rcases hrs with rfl | rfl <;> decide
  have hn := hp.n16
  have hin : ∀ k < rs.length, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => by
      rw [hI.rd, hI.wr, hI.x2, Offset.add_add_eq _ (show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega)]
      exact ⟨_, List.mem_append_right _ hp.dat, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (ldData_ok rs 0 s hbr.1 (by omega) hin) fun s₁ ⟨e₁, f₁⟩ => ?_)
  have hK₁ := B.of_v hI.keys hbr f₁.v (f₁.gpr _ (by simp)) (f₁.gpr _ (by simp))
  refine WP.seq (WP.mono (B.ok hbr hK₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  rw [WP.block_append_iff]
  have hx2 : s₂.gpr .x2 = bdp s₀ + BitVec.ofNat 64 (16 * c) := by
    rw [f₂.gpr, f₁.gpr _ (by simp), hI.x2]
  have hF : ∀ k (h : k < rs.length), ∀ t < 16,
      vbyte (s₂.v rs[k]) t = (ecbOut B.F s₀.mem (bdp s₀) (bnr s₀) (bsch s₀) (c + 0 + k)).getD t 0 := by
    intro k h t ht
    rw [← getD_st _ ht, e₂ _ (List.getElem_mem h), e₁ k h, st_readW, hI.x2,
      Offset.add_add_eq _ (show 16 * c + 16 * (0 + k) = 16 * (c + 0 + k) by omega),
      ecbInv_orig hI.data (by omega) (by omega)]
    rfl
  refine WP.mono (stData_ok (m₀ := s₀.mem) (D := bdp s₀) (c := c) hp.nb16 rs 0 s₂ hx2 (by omega)
      (by omega) (by rw [f₂.wr, f₁.wr, hI.wr]; exact hp.dat)
      (by rw [f₂.mem, f₁.mem, Nat.add_zero]; exact hI.data) hF)
    fun s₃ ⟨d₃, fr₃, g₃, v₃, sp₃, rd₃, wr₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have g : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, f₁.gpr r (by simp)]
  refine ⟨hc, ?_, by rw [g]; exact hI.x2, by rw [g]; exact hI.x3,
    by rw [hm₂] at fr₃; exact hI.frame.trans fr₃, by rw [Nat.add_zero] at d₃; exact d₃,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩
  exact B.of_v (B.of_v hK₁ hbr f₂.v (by rw [f₂.gpr]) (by rw [f₂.gpr])) hbr
    (fun r _ => by rw [v₃]) (by rw [g₃]) (by rw [g₃])

theorem btail8_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {c : Nat} (hc : c + 8 ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ (c + 8) c s) :
    WP isa (.block [.addImm .x .x2 .x2 128, .subImm .x .x3 .x3 8, .lsr .x .x13 .x3 3]) s fun s' =>
      BInv B s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((bnb s₀ - (c + 8)) / 8) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  have h4 : BitVec.ofNat 64 (bnb s₀ - c) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (bnb s₀ - (c + 8)) := by
    rw [Offset.ofNat_sub_ofNat (by omega), show bnb s₀ - c - 8 = bnb s₀ - (c + 8) by omega]
  refine ⟨⟨hI.le, B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_, ?_, hI.frame, hI.data, hI.rd, hI.wr⟩, ?_⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    exact Offset.add_add_eq _ (by omega)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    exact h4
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    rw [h4, ushr3 (by omega)]

theorem btail1_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {c : Nat} (hc : c + 1 ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ (c + 1) c s) :
    WP isa (.block [.addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1]) s (BInv B s₀ (c + 1) (c + 1)) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨hI.le, B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_, ?_, hI.frame, hI.data, hI.rd, hI.wr⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    exact Offset.add_add_eq _ (by omega)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    rw [Offset.ofNat_sub_ofNat (by omega), show bnb s₀ - c - 1 = bnb s₀ - (c + 1) by omega]

theorem blk8_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {c : Nat} (hc : c + 8 ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ c c s) :
    WP isa (blk8 B.f) s fun s' =>
      BInv B s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((bnb s₀ - (c + 8)) / 8) :=
  group_ok B hp regs8 (.inl rfl) _ hc hI fun _ hI' => btail8_ok B hp hc hI'

theorem blk1_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {c : Nat} (hc : c + 1 ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ c c s) : WP isa (blk1 B.f) s (BInv B s₀ (c + 1) (c + 1)) :=
  group_ok B hp [.v0] (.inr rfl) _ hc hI fun _ hI' => btail1_ok B hp hc hI'

/-- The loops, from the state after the setup. -/
theorem loops_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {s₁ : State} (hI₁ : BInv B s₀ 0 0 s₁)
    (h13 : s₁.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)) :
    WP isa (.seq (.ite (.zero .x .x13) (.block []) (.loop (blk8 B.f) (.nonzero .x .x13)))
      (.ite (.zero .x .x3) (.block []) (.loop (blk1 B.f) (.nonzero .x .x3)))) s₁
      (BInv B s₀ (bnb s₀) (bnb s₀)) := by
  have hn := hp.n16
  refine WP.seq (WP.mono (Q := fun s => ∃ c, bnb s₀ - c < 8 ∧ BInv B s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (bnb s₀ / 8 = 0)) (eval_zero h13 (by omega)) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simp at h; omega, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = bnb s₀ - c ∧ c + 8 ≤ bnb s₀ ∧ BInv B s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (blk8 B.f) s (fun s' =>
          (AArch64.eval (.nonzero .x .x13) s' = some false ∧ ∃ c, bnb s₀ - c < 8 ∧ BInv B s₀ c c s') ∨
          (AArch64.eval (.nonzero .x .x13) s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (blk8_ok B hp hc hI) fun s' ⟨hI', h13'⟩ => ?_
        rw [eval_nonzero h13' (by omega)]
        by_cases hlt : bnb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp; omega, c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp; omega, bnb s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I8 hstep (bnb s₀) s₁ ⟨0, rfl, by simp at h; omega, hI₁⟩
  refine WP.ite (decide (bnb s₀ - c = 0)) (eval_zero hI₂.x3 (by omega)) (fun h => ?_) (fun h => ?_)
  · have : c = bnb s₀ := by have := hI₂.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = bnb s₀ - c ∧ c < bnb s₀ ∧ BInv B s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blk1 B.f) s (fun s' =>
        (AArch64.eval (.nonzero .x .x3) s' = some false ∧ BInv B s₀ (bnb s₀) (bnb s₀) s') ∨
        (AArch64.eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (blk1_ok B hp hc hI) fun s' hI' => ?_
      rw [eval_nonzero hI'.x3 (by omega)]
      by_cases hlast : bnb s₀ - (c + 1) = 0
      · have : c + 1 = bnb s₀ := by omega
        exact .inl ⟨by simp [hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [hlast], bnb s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < bnb s₀ := by have := hI₂.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (bnb s₀ - c) s₂ ⟨c, rfl, hlt, hI₂⟩

/-! ## The setups -/

/-- What `keysCommon` leaves. -/
structure Common (s₀ s : State) : Prop where
  kreg : ∀ j < 13, s.v (kreg j) = s₀.mem.readW (bkp s₀ + BitVec.ofNat 64 (16 * j)) 128
  v30 : s.v .v30 = s₀.mem.readW (bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀)) 128
  x9 : s.gpr .x9 = bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀)
  x6 : s.gpr .x6 = BitVec.ofNat 64 (bnr s₀) - 10
  x7 : s.gpr .x7 = BitVec.ofNat 64 (bnr s₀) - 12
  x13 : s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)
  gpr : ∀ r, r ≠ .x9 → r ≠ .x6 → r ≠ .x7 → r ≠ .x13 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem common_ok {s₀ : State} (hp : BPre s₀) : WP isa (.block keysCommon) s₀ (Common s₀) := by
  have hR := hp.rounds
  have hn := hp.nb16
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (bnr s₀) := by simp [bnr]
  have hx3 : s₀.gpr .x3 = BitVec.ofNat 64 (bnb s₀) := by simp [bnb]
  rw [keysCommon, WP.block_append_iff]
  refine WP.mono (loads_ok s₀ (fun j hj => hp.key_in (by omega)) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) := by
    rw [g, g, shl4]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact hp.key_in (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, f₁.rd, f₁.wr⟩
  · simp only [State.setV, State.write, (kreg_ne j).2, ite_false]
    rw [e₁ j hj]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, f₁.mem]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx3]
    exact ushr3 (by omega)
  · simp only [State.setV, State.write, h1, h2, h3, h4, ite_false, g]
  · exact f₁.mem

theorem encSetup_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block encSetup) s₀ fun s => BInv encFn s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8) := by
  have hR := hp.rounds
  rw [encSetup, WP.block_append_iff]
  refine WP.mono (common_ok hp) fun s₁ c₁ => ?_
  have e9' : bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) - BitVec.ofNat 64 16 =
      bkp s₀ + BitVec.ofNat 64 (16 * (bnr s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega), show 16 * bnr s₀ - 16 = 16 * (bnr s₀ - 1) by omega]
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9,
      e9', BitVec.add_zero, c₁.rd, c₁.wr]
    exact hp.key_in (by omega)), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega
  refine ⟨⟨Nat.zero_le _, ⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, ite_false]
    rw [c₁.kreg j (by omega)]
    exact keyIs_readW _ _ (hL j (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9, e9',
      BitVec.add_zero, c₁.mem]
    exact keyIs_readW _ _ (hL _ (by omega))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x6]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x7]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp
  · simp only [State.setV, State.write, reduceCtorEq, ite_false]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp [bnb]
  · simp only [State.setV, State.write, c₁.mem]; exact Frame.refl _ _
  · intro i hi
    simp only [State.setV, State.write, c₁.mem]
    rw [ite_eq_right (by omega)]
  · simp only [State.setV, State.write, c₁.rd]
  · simp only [State.setV, State.write, c₁.wr]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x13]

theorem dreg_inj : ∀ j < 13, ∀ i < 13, dreg (j + 1) = dreg (i + 1) → j = i := by decide

/-- `aesimc` of the first `k` middle round keys. -/
theorem imcs_ok (s : State) :
    ∀ k ≤ 13, WP isa (.block ((List.range k).map fun j => .vop (.aesimc (dreg (j + 1)) (dreg (j + 1))))) s
      fun s' => (∀ j < 13, s'.v (dreg (j + 1)) =
          if j < k then aesInvMixColumns (s.v (dreg (j + 1))) else s.v (dreg (j + 1))) ∧
        (∀ r, (∀ j < 13, r ≠ dreg (j + 1)) → s'.v r = s.v r) ∧
        s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun j _ => by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (imcs_ok s k (by omega)) fun s₁ ⟨e₁, o₁, g₁, m₁, rd₁, wr₁⟩ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, isa, exec,
        VOp.eval, Option.map_some]; rfl, ?_⟩
    refine ⟨fun j hj => ?_, fun r hr => ?_, g₁, m₁, rd₁, wr₁⟩
    · by_cases hjk : j = k
      · subst hjk
        rw [setV_v_self, e₁ j hj, ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [setV_v_of_ne _ _ fun h => hjk (dreg_inj j hj k (by omega) h), e₁ j hj]
        by_cases hjk' : j < k
        · rw [ite_eq_left hjk', ite_eq_left (by omega)]
        · rw [ite_eq_right hjk', ite_eq_right (by omega)]
    · rw [setV_v_of_ne _ _ (hr k (by omega)), o₁ r hr]

theorem dreg_ne : ∀ j < 13, dreg (j + 1) ≠ .v30 ∧ dreg (j + 1) ≠ .v16 := by decide

theorem decSetup_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block decSetup) s₀ fun s => BInv decFn s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8) := by
  have hR := hp.rounds
  rw [decSetup, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (common_ok hp) fun s₁ c₁ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 208) (by decide) (by
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide), c₁.rd, c₁.wr]
    exact hp.key_in (by omega)), WP.block_nil ?_⟩
  refine WP.mono (imcs_ok _ 13 (Nat.le_refl _)) fun s₂ ⟨e₂, o₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  have hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega
  have x0 : s₁.gpr .x0 = bkp s₀ := c₁.gpr _ (by decide) (by decide) (by decide) (by decide)
  -- The middle round keys, before `aesimc`.
  have pre : ∀ j, 1 ≤ j → j ≤ 13 → j < bnr s₀ →
      KeyIs ((s₁.setV .v29 (s₁.mem.readW (s₁.gpr .x0 + BitVec.ofNat 64 208) 128)).v (dreg j))
        (roundKey (bsch s₀) j) := by
    intro j h1 h2 h3
    by_cases h13 : j = 13
    · subst h13
      simp only [Impl.Aes.AArch64.Aese.dreg, ite_true, setV_v_self, x0, c₁.mem]
      have := keyIs_readW s₀.mem (bkp s₀) (L := 16 * (bnr s₀ + 1)) (j := 13) (hL 13 (by omega))
      simpa using this
    · simp only [Impl.Aes.AArch64.Aese.dreg, h13, ite_false]
      rw [setV_v_of_ne _ _ (kreg_ne j).1, c₁.kreg j (by omega)]
      exact keyIs_readW _ _ (hL j (by omega))
  refine ⟨⟨Nat.zero_le _, ⟨hR, ?_, fun j h1 h2 => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o₂ _ fun j hj => (dreg_ne j hj).1.symm, setV_v_of_ne _ _ (by decide), c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · have hj13 : j ≤ 13 := by omega
    have := e₂ (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega, ite_eq_left (by omega)] at this
    rw [this]
    exact keyIs_aesimc (pre j h1 hj13 h2)
  · rw [o₂ _ fun j hj => (dreg_ne j hj).2.symm, setV_v_of_ne _ _ (by decide)]
    have := c₁.kreg 0 (by omega)
    simp only [Impl.Aes.AArch64.Aese.kreg] at this
    rw [this]
    exact keyIs_readW _ _ (hL 0 (by omega))
  · rw [g₂]; simp only [State.setV]; exact c₁.x6
  · rw [g₂]; simp only [State.setV]; exact c₁.x7
  · rw [g₂]; simp only [State.setV]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp
  · rw [g₂]; simp only [State.setV]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp [bnb]
  · rw [m₂]; simp only [State.setV, c₁.mem]; exact Frame.refl _ _
  · intro i hi
    rw [m₂]; simp only [State.setV, c₁.mem]
    rw [ite_eq_right (by omega)]
  · rw [rd₂]; simp only [State.setV, c₁.rd]
  · rw [wr₂]; simp only [State.setV, c₁.wr]
  · rw [g₂]; simp only [State.setV, c₁.x13]

/-! ## The whole functions -/

theorem post_of (B : BlockFn) {s₀ : State} {s : State} (hI : BInv B s₀ (bnb s₀) (bnb s₀) s) :
    (Proof.Aes.blocksAArch64 B.F).post s₀ s := by
  show Spec.Aes.statesAt s.mem (bdp s₀) (bnb s₀) = _
  rw [Proof.Aes.AArch64.statesAt_of_ecbInv hI.data]
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

theorem bcorrect (B : BlockFn) {setup : List Instr} {s₀ : State} (hp : BPre s₀)
    (hs : WP isa (.block setup) s₀ fun s => BInv B s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)) :
    WP isa (blocks setup B.f) s₀ ((Proof.Aes.blocksAArch64 B.F).post s₀) :=
  WP.seq (WP.mono hs fun _ ⟨hI₁, h13⟩ => WP.mono (loops_ok B hp hI₁ h13) fun _ hI => post_of B hI)

theorem blocks_correct (B : BlockFn) {setup : List Instr}
    (hs : ∀ s₀, BPre s₀ → WP isa (.block setup) s₀ fun s =>
      BInv B s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8))
    (hg : (blocks setup B.f).allInstrs (fun i => preserved.all fun r => dstOf i != some r) = true)
    (hnc : (blocks setup B.f).noCalls = true) (hv : (blocks setup B.f).allInstrs keepsV = true)
    (s : State) (hp : (Proof.Aes.blocksAArch64 B.F).pre s) :
    ∃ t s', Exec isa (blocks setup B.f) s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 B.F).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved) (bcorrect B (bpre_of hp) (hs s (bpre_of hp))) hg hnc
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he hv⟩, h₂⟩

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' :=
  blocks_correct encFn (fun _ hp => encSetup_ok hp) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) s hs

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s s' :=
  blocks_correct decFn (fun _ hp => decSetup_ok hp) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) s hs

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocks_verified :
    Verified AArch64.target encryptBlocks (Spec.Aes.encryptBlocksContract AArch64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Aes.AArch64.blocksSat] using Proof.Aes.AArch64.blocksSat)

theorem decryptBlocks_verified :
    Verified AArch64.target decryptBlocks (Spec.Aes.decryptBlocksContract AArch64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Aes.AArch64.blocksSat] using Proof.Aes.AArch64.blocksSat)

end VG.Proof.Aes.AArch64.Aese
