import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Aes.X86.Ctr32
import VerifiedGarbage.Impl.Aes.X86.Linear
import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Impl.Aes.X86.Sbox
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Aes.Ct32.InvBitsliced
import VerifiedGarbage.Proof.Framework.X86.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Impl.Aes.X86.Blocks

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Common`. -/
section

/-!
# AES and GHASH on x86 (32-bit): regions of 32-bit buffers

Parts of a buffer at a 32-bit address `b` that does not wrap around the
(32-bit) address space: which parts contain which accesses, and which are
disjoint. The single-instruction weakest-precondition rules are
`Proof/Framework/X86/Wp.lean`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86

/-- The region of `n` bytes at a 32-bit pointer. -/
abbrev reg32 (b : BitVec 32) (n : Nat) : Region := ⟨b.setWidth 64, n⟩

theorem addr_zero (b : BitVec 32) : VG.X86.addr b 0 = b.setWidth 64 := by simp [VG.X86.addr]

theorem toNat_setWidth32 (b : BitVec 32) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- The `n` bytes at offset `o` of a buffer at `b` are within its part at offset `a`. -/
theorem part_contains {b : BitVec 32} {N a k o n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hak : a + k ≤ N)
    (h1 : a ≤ o) (h2 : o + n ≤ a + k) (hn : 0 < n) : (⟨VG.X86.addr b a, k⟩ : Region).Contains (VG.X86.addr b o) n := by
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega)]
  have hE := VG.Proof.Aes.X86.toNat_setWidth32 b
  generalize b.setWidth 64 = E at *
  bv_omega

theorem reg_contains {b : BitVec 32} {N o n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (h : o + n ≤ N)
    (hn : 0 < n) : (VG.Proof.Aes.X86.reg32 b N).Contains (VG.X86.addr b o) n := by
  have := VG.Proof.Aes.X86.part_contains (a := 0) (k := N) hfit (by omega) (Nat.zero_le o) (by omega) hn
  rwa [VG.Proof.Aes.X86.addr_zero] at this

theorem in_reg {rs : List Region} {b : BitVec 32} {N : Nat} (hr : VG.Proof.Aes.X86.reg32 b N ∈ rs)
    (hfit : b.toNat + N ≤ 2 ^ 32) {o n : Nat} (h : o + n ≤ N) (hn : 0 < n) : InRegions rs (VG.X86.addr b o) n :=
  ⟨_, hr, VG.Proof.Aes.X86.reg_contains hfit h hn⟩

theorem in_rd {rs rs' : List Region} {a : Addr} {n : Nat} (h : InRegions rs' a n) :
    InRegions (rs ++ rs') a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem in_rd_left {rs rs' : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    InRegions (rs ++ rs') a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_left _ hr, hc⟩

/-- Two parts of a buffer at `b` that do not overlap. -/
theorem part_disj {b : BitVec 32} {N a n c k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (ha : a + n ≤ N)
    (hc : c + k ≤ N) (h : a + n ≤ c ∨ c + k ≤ a) :
    Region.Disjoint ⟨VG.X86.addr b a, n⟩ ⟨VG.X86.addr b c, k⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  by_cases hn : n = 0
  · omega
  by_cases hk : k = 0
  · omega
  rw [addr_eq (by omega)] at h₁
  rw [addr_eq (by omega)] at h₂
  have hE := VG.Proof.Aes.X86.toNat_setWidth32 b
  generalize b.setWidth 64 = E at *
  rcases h with h | h <;> bv_omega

/-- A part of a buffer at `b` within another. -/
theorem part_sub {b : BitVec 32} {N a n c k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hc : c + k ≤ N)
    (h1 : c ≤ a) (h2 : a + n ≤ c + k) : Region.Sub ⟨VG.X86.addr b a, n⟩ ⟨VG.X86.addr b c, k⟩ := by
  intro x h
  simp only [Region.Contains] at h ⊢
  by_cases hn : n = 0
  · omega
  rw [addr_eq (by omega)] at h ⊢
  have hE := VG.Proof.Aes.X86.toNat_setWidth32 b
  generalize b.setWidth 64 = E at *
  bv_omega

theorem part_sub_reg {b : BitVec 32} {N a n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (h : a + n ≤ N) :
    Region.Sub ⟨VG.X86.addr b a, n⟩ (VG.Proof.Aes.X86.reg32 b N) := by
  have := VG.Proof.Aes.X86.part_sub (c := 0) (k := N) (a := a) (n := n) hfit (by omega) (Nat.zero_le _) (by omega)
  rwa [VG.Proof.Aes.X86.addr_zero] at this

theorem addr_add (b : BitVec 32) (a o : Nat) : VG.X86.addr (b + BitVec.ofNat 32 a) o = VG.X86.addr b (a + o) := by
  simp only [VG.X86.addr]; rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Words of a buffer -/

theorem rd_wr_other {m : Mem} {a b : Addr} {v : BitVec 32} {r₁ r₂ : Region} (h : r₁.Disjoint r₂)
    (ha : r₁.Contains a (32 / 8)) (hb : r₂.Contains b (32 / 8)) : (m.writeW b v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (h.sep ha hb) (by decide)

theorem frame_one {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {r : Region}
    (hc : r.Contains a 1) (hd : ∀ r' ∈ rs, r.Disjoint r') : m' a = m a :=
  hf a fun r' hr' hc' => hd r' hr' a hc hc'

/-- A word of a 32-bit buffer, after writing a word of it. -/
theorem rd_wr {B : BitVec 32} {N : Nat} (hfit : B.toNat + N ≤ 2 ^ 32) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ N) (he : e + 4 ≤ N) (hd4 : d % 4 = 0) (he4 : e % 4 = 0) :
    (m.writeW (VG.X86.addr B e) v).readW (VG.X86.addr B d) 32 = if d = e then v else m.readW (VG.X86.addr B d) 32 := by
  split
  · subst_vars; exact Mem.readW_writeW_self32 _ _ _
  · refine Mem.readW_writeW_sep (Region.Disjoint.sep (r₁ := ⟨VG.X86.addr B d, 4⟩) (r₂ := ⟨VG.X86.addr B e, 4⟩)
      (VG.Proof.Aes.X86.part_disj hfit hd he (by omega)) (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)

theorem rd_wr_ne {B : BitVec 32} {N : Nat} (hfit : B.toNat + N ≤ 2 ^ 32) (m : Mem) (v : BitVec 32)
    {d e : Nat} (hd : d + 4 ≤ N) (he : e + 4 ≤ N) (hd4 : d % 4 = 0) (he4 : e % 4 = 0) (hne : d ≠ e) :
    (m.writeW (VG.X86.addr B e) v).readW (VG.X86.addr B d) 32 = m.readW (VG.X86.addr B d) 32 := by
  rw [VG.Proof.Aes.X86.rd_wr hfit m v hd he hd4 he4, ite_eq_right hne]

theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (first | omega | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega))

/-- Bit `8 i + t` of a little-endian word is bit `t` of its byte `i`. -/
theorem readW_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 4) (ht : t < 8) :
    (m.readW a 32).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 4) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 32 by omega]

theorem addr_add64 {S : BitVec 32} {x y : Nat} (h : S.toNat + x + y < 2 ^ 32) :
    VG.X86.addr S x + BitVec.ofNat 64 y = VG.X86.addr S (x + y) := by
  rw [addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Sbox`. -/
section

/-!
# The bitsliced S-box on x86 (32-bit)

`sboxCode` only combines words bitwise, so it computes the same Boolean
function at each of the 32 bit positions: the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's S-box on the same tables (`sboxT`, proved right in
`Proof/Aes/SboxSpec.lean`). `sbox_ok` then gives, at every bit position
`p`, the S-box of the byte formed by bit `p` of the eight words in slots
`0 … 7`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (sbox)

/-- The memory of the layers: the state and the S-box's spill slots, 256
bytes at `edi`. -/
def linCfg : Cfg := { base := sb, slots := 64, ext := sb, exts := 0 }

/-- The words of the state: slots `0 … 7`. -/
abbrev Q (s : State) (j : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) j) 32

/-- The truth table of bit `k` of the input. -/
def inT (k : Nat) : Nat := tableOf (fun c => c.testBit k) 256

def inTs : List Nat := (List.range 8).map VG.Proof.Aes.X86.inT

def sboxEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if k < 8 then some (VG.Proof.Aes.X86.inT k) else none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.slot j == some ((sboxT VG.Proof.Aes.X86.inTs).getD j 0)

theorem sbox_check :
    VG.X86.Straight.check (table 32 256) VG.Proof.Aes.X86.linCfg (fun _ => none) sboxCode VG.Proof.Aes.X86.sboxEnv VG.Proof.Aes.X86.sboxPost = true := by
  decide +kernel

theorem row_inTs {c : Nat} (hc : c < 256) : row VG.Proof.Aes.X86.inTs c = BitVec.ofNat 8 c := by
  refine row_ext fun j hj => ?_
  simp only [VG.Proof.Aes.X86.inTs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, VG.Proof.Aes.X86.inT, testBit_tableOf, hc, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, hj]

/-- The registers the layers may write are `tmpRegs`. -/
theorem not_tmp (r : Reg) (hr : r ∉ tmpRegs) : r ∈ [Reg.esp, .esi, .edi] := by
  revert hr; cases r <;> decide

theorem keeps_rest {is : List Instr}
    (h : [Reg.esp, .esi, .edi].all (fun r => is.all fun i => i.dst != some r) = true)
    (r : Reg) (hr : r ∉ tmpRegs) : (is.all fun i => i.dst != some r) = true :=
  List.all_eq_true.mp h r (VG.Proof.Aes.X86.not_tmp r hr)

/-- The S-box, at every bit position of the words in slots `0 … 7`. -/
theorem sbox_ok {s : State} (hok : Ok VG.Proof.Aes.X86.linCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p = (sbox (bsByte (VG.Proof.Aes.X86.Q s) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.X86.sbox_check
  have hout : ∀ j < 8, e'.slot j = some ((sboxT VG.Proof.Aes.X86.inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  -- The run at bit position `p`, on the input formed by the bits `p`.
  have key : ∀ p < 32, ∃ s', runBlock isa sboxCode s = some s' ∧
      Post (TableRel p (bsByte (VG.Proof.Aes.X86.Q s) p).toNat) VG.Proof.Aes.X86.linCfg (fun _ => none) e' s s'
        (fun r => (sboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (VG.Proof.Aes.X86.Q s) p).isLt
    refine run (table_sound hp hc) hok ⟨(fun r a h => by cases h), fun k a _ h => ?_,
      (fun _ _ _ h => by cases h)⟩ he
    simp only [VG.Proof.Aes.X86.sboxEnv] at h
    split at h
    · rename_i hk8
      cases h
      simp only [TableRel, VG.Proof.Aes.X86.inT, testBit_tableOf, hc, decide_true, Bool.true_and,
        BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, VG.Proof.Aes.X86.Q, VG.Proof.Aes.X86.linCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (VG.Proof.Aes.X86.Q s) p).isLt
    have := p₁.rel.slot j _ (by simp [VG.Proof.Aes.X86.linCfg]; omega) (hout j hj)
    have hb : s''.gpr sb = s.gpr sb := p₁.base
    simp only [TableRel, VG.Proof.Aes.X86.linCfg, hb] at this
    rw [VG.Proof.Aes.X86.Q, hb, ← this, ← getLsbD_row _ _ hj,
      row_sboxT (by simp [VG.Proof.Aes.X86.inTs]) hc, VG.Proof.Aes.X86.row_inTs hc]
    simp
  · have : (sboxCode.all fun i => i.dst != some r) = true :=
      VG.Proof.Aes.X86.keeps_rest (by decide +kernel) r hr
    simp [this]

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Linear`. -/
section

/-!
# The linear layers of bitsliced AES on x86 (32-bit)

Each layer is checked by evaluation over the lane domain
(`Framework/X86/Linear.lean`): the kernel runs it on the input words (the
slots `0 … 7`, and for AddRoundKey the round key at `kp`) as atoms and
compares every output bit with the XOR of input bits given in
`Proof/Aes/Ct32/Layers.lean`. Position `p = 8r + 2c + b` of a word of the
bitsliced state is byte `r + 4c` of block `b`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32

/-- AddRoundKey's memory: the state, and the round key at `kp`. -/
def arkCfg : Cfg := { base := sb, slots := 8, ext := kp, exts := 8 }

/-- The state slots hold input words `0 … 7`. -/
def qIns : List (Nat × Nat) := (List.range 8).map fun k => (k, k)

/-- The output slots `j`, bit `p` the XOR of the input bits `g j p`. -/
def qOuts (g : Nat → Nat → List Nat) : List (Nat × (Nat → List Nat)) :=
  (List.range 8).map fun j => (j, g j)

theorem ortho_toBs_check :
    VG.X86.Straight.check (lanes 32 8) VG.Proof.Aes.X86.linCfg (linExt 0) ortho (linEnv VG.Proof.Aes.X86.qIns) (linPost 64 8 (VG.Proof.Aes.X86.qOuts toBsG)) = true := by
  decide +kernel

theorem ortho_fromBs_check :
    VG.X86.Straight.check (lanes 32 8) VG.Proof.Aes.X86.linCfg (linExt 0) ortho (linEnv VG.Proof.Aes.X86.qIns) (linPost 64 8 (VG.Proof.Aes.X86.qOuts fromBsG)) = true := by
  decide +kernel

theorem shiftRows_check :
    VG.X86.Straight.check (lanes 32 8) VG.Proof.Aes.X86.linCfg (linExt 0) shiftRows (linEnv VG.Proof.Aes.X86.qIns) (linPost 64 8 (VG.Proof.Aes.X86.qOuts srG)) = true := by
  decide +kernel

theorem mixColumns_check :
    VG.X86.Straight.check (lanes 32 8) VG.Proof.Aes.X86.linCfg (linExt 0) mixColumns (linEnv VG.Proof.Aes.X86.qIns) (linPost 64 8 (VG.Proof.Aes.X86.qOuts mcG)) = true := by
  decide +kernel

theorem addRoundKey_check :
    VG.X86.Straight.check (lanes 32 9) VG.Proof.Aes.X86.arkCfg (linExt 8) addRoundKey (linEnv VG.Proof.Aes.X86.qIns) (linPost 8 9 (VG.Proof.Aes.X86.qOuts arkG)) = true := by
  decide +kernel

/-! ## On the machine -/

theorem q_linear {k xb : Nat} {c : Cfg} {is : List Instr} {g : Nat → Nat → List Nat}
    (hchk : VG.X86.Straight.check (lanes 32 k) c (linExt xb) is (linEnv VG.Proof.Aes.X86.qIns) (linPost c.slots k (VG.Proof.Aes.X86.qOuts g)) = true)
    (hk : 256 ≤ 2 ^ k) (hcb : c.base = sb)
    (hw : [Reg.esp, .esi, .edi].all (fun r => is.all fun i => i.dst != some r) = true)
    {s : State} (hok : Ok c s) (W : Nat → BitVec 32) (hW : ∀ i < 8, W i = VG.Proof.Aes.X86.Q s i)
    (hext : ∀ j < c.exts,
      32 * (xb + j) + 32 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 32) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p = xorBits W (g j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok hchk hok W (fun j i hji _ => by
    simp only [VG.Proof.Aes.X86.qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
    obtain ⟨i, hi, rfl, rfl⟩ := hji
    exact ⟨by omega, by rw [hW i hi, hcb]⟩) hext
  have hmem : ∀ j < 8, (j, g j) ∈ VG.Proof.Aes.X86.qOuts g := fun j hj => by
    simp only [VG.Proof.Aes.X86.qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  have hsb : s'.gpr sb = s.gpr sb := hoth sb (VG.Proof.Aes.X86.keeps_rest hw sb (by decide))
  refine ⟨s', hs', fun j hj p hp => ?_, hrd, hwr, fun r hr => hoth r (VG.Proof.Aes.X86.keeps_rest hw r hr), hfr⟩
  have := hout j (g j) (hmem j hj) p hp
  rw [hcb] at this
  rw [VG.Proof.Aes.X86.Q, hsb]; exact this

theorem toBs_ok {s : State} (hok : Ok VG.Proof.Aes.X86.linCfg s) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p =
        (VG.Proof.Aes.X86.Q s (p % 2 + 2 * (idx p / 4))).getLsbD (8 * (idx p % 4) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.X86.q_linear VG.Proof.Aes.X86.ortho_toBs_check (by decide) rfl
    (by decide +kernel) hok (VG.Proof.Aes.X86.Q s) (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.X86.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by omega)]

theorem fromBs_ok {s : State} (hok : Ok VG.Proof.Aes.X86.linCfg s) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ k < 8, ∀ t < 32, (VG.Proof.Aes.X86.Q s' k).getLsbD t = (VG.Proof.Aes.X86.Q s (t % 8)).getLsbD (pos (k % 2) (t / 8 + 4 * (k / 2)))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.X86.q_linear VG.Proof.Aes.X86.ortho_fromBs_check (by decide) rfl
    (by decide +kernel) hok (VG.Proof.Aes.X86.Q s) (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.X86.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [pos]; omega)]

theorem shiftRows_ok {s : State} (hok : Ok VG.Proof.Aes.X86.linCfg s) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p = (VG.Proof.Aes.X86.Q s j).getLsbD (srSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.X86.q_linear VG.Proof.Aes.X86.shiftRows_check (by decide) rfl
    (by decide +kernel) hok (VG.Proof.Aes.X86.Q s) (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.X86.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, srG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [srSrc]; omega)]

theorem mixColumns_ok {s : State} (hok : Ok VG.Proof.Aes.X86.linCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p = termsXor (VG.Proof.Aes.X86.Q s) (mcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.X86.q_linear VG.Proof.Aes.X86.mixColumns_check (by decide) rfl
    (by decide +kernel) hok (VG.Proof.Aes.X86.Q s) (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.X86.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, mcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-- Word `j` of the bitsliced round key at `kp`. -/
abbrev keyWord (s : State) (j : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr kp) j) 32

theorem addRoundKey_ok {s : State} (hok : Ok VG.Proof.Aes.X86.arkCfg s) :
    ∃ s', runBlock isa addRoundKey s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p = ((VG.Proof.Aes.X86.Q s j).getLsbD p ^^ (VG.Proof.Aes.X86.keyWord s j).getLsbD p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.arkCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i < 8 then VG.Proof.Aes.X86.Q s i else VG.Proof.Aes.X86.keyWord s (i - 8)
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.X86.q_linear VG.Proof.Aes.X86.addRoundKey_check (by decide) rfl
    (by decide +kernel) hok W
    (fun i hi => by simp [W, hi]) (fun j hj => by
      simp only [VG.Proof.Aes.X86.arkCfg] at hj ⊢
      refine ⟨by omega, ?_⟩
      simp [W, show ¬ 8 + j < 8 by omega])
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, arkG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
  simp [W, hj, show ¬ 8 + j < 8 by omega]

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Encrypt`. -/
section

/-!
# Encrypting two blocks, bitsliced, on x86 (32-bit)

`encrypt2_ok`: from two blocks in slots `0 … 7` (`InRel`), with the
bitsliced round keys in the scratch buffer (`KeysAt`), `encrypt2` leaves
the two ciphertexts, having written only the first 256 bytes of the scratch
buffer. The layers are composed from their proofs (`Sbox.lean`,
`Linear.lean`); the round loop's invariant is the specification's `foldl`
over the rounds done.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (roundKey subBytes shiftRows mixColumns addRoundKey cipher)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_bswap wp_ldm wp_xorm wp_stm sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-- The offset of bitsliced round key `j` of `R` in the scratch buffer. -/
def keyOff (R j : Nat) : Nat := lastKey - 32 * (R - j)

/-- The bitsliced round keys `0 … R` of the schedule `w`, in the scratch buffer at `B`. -/
def KeysAt (m : Mem) (B : BitVec 32) (R : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ R, KeyRel (fun k => m.readW (VG.X86.addr B (VG.Proof.Aes.X86.keyOff R j + 4 * k)) 32) (roundKey w j)

/-- What encryption needs: the scratch buffer (2048 bytes at `edi`) is
writable, the round keys are in it, and `rounds` is the second argument. -/
structure EncPre (s₀ : State) (R : Nat) (w : List Byte) : Prop where
  scr : VG.Proof.Aes.X86.reg32 (s₀.gpr sb) 2048 ∈ s₀.wr
  fit : (s₀.gpr sb).toNat + 2048 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  argIn : InRegions (s₀.rd ++ s₀.wr) (VG.X86.addr (s₀.gpr .esp) 8) 4
  argR : s₀.mem.readW (VG.X86.addr (s₀.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  argSep : Region.Disjoint ⟨VG.X86.addr (s₀.gpr .esp) 8, 4⟩ (VG.Proof.Aes.X86.reg32 (s₀.gpr sb) 256)
  keys : VG.Proof.Aes.X86.KeysAt s₀.mem (s₀.gpr sb) R w

/-- What stays the same during encryption. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ tmpRegs → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.Aes.X86.reg32 (s₀.gpr sb) 256] s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : VG.Proof.Aes.X86.Ctx s₀ s₀ := ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : VG.Proof.Aes.X86.Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

theorem Ctx.esp {s₀ s : State} (hc : VG.Proof.Aes.X86.Ctx s₀ s) : s.gpr .esp = s₀.gpr .esp :=
  hc.keep _ (by decide) (by decide)

theorem Ctx.step {s₀ s s' : State} (hc : VG.Proof.Aes.X86.Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hoth : ∀ r, r ∉ tmpRegs → r ≠ kp → s'.gpr r = s.gpr r)
    (hfr : Frame [VG.Proof.Aes.X86.reg32 (s.gpr sb) 256] s.mem s'.mem) : VG.Proof.Aes.X86.Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 => (hoth r h1 h2).trans (hc.keep r h1 h2),
    hc.frame.trans (by rw [← hc.base]; exact hfr)⟩

/-- A step that writes only a register of `tmpRegs` or `kp`. -/
theorem Ctx.upd {s₀ s s' : State} {d : Reg} {v : BitVec 32} (hc : VG.Proof.Aes.X86.Ctx s₀ s) (u : Upd s s' d v)
    (hd : d ∈ tmpRegs ∨ d = kp) : VG.Proof.Aes.X86.Ctx s₀ s' :=
  hc.step u.rd u.wr (fun r h1 h2 => u.other r (by rintro rfl; rcases hd with h | h <;> simp_all))
    (by rw [u.mem]; exact Frame.refl _ _)

theorem Ctx.linOk {s₀ s : State} {R : Nat} {w : List Byte} (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s) : Ok VG.Proof.Aes.X86.linCfg s :=
  Ok.of_off (r := VG.Proof.Aes.X86.reg32 (s₀.gpr sb) 2048) (r' := VG.Proof.Aes.X86.reg32 (s₀.gpr sb) 2048) (b := s₀.gpr sb)
    (b' := s₀.gpr sb) (off := 0) (off' := 0) (n := 2048) (n' := 2048)
    (by rw [hc.wr]; exact hp.scr) rfl hp.fit (Nat.le_refl _)
    (by show s.gpr sb = _; rw [hc.base]; simp) (by simp [VG.Proof.Aes.X86.linCfg])
    (by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hp.scr) rfl hp.fit (Nat.le_refl _)
    (by rw [show linCfg.ext = sb from rfl, hc.base]; simp) (by simp [VG.Proof.Aes.X86.linCfg])
    (.inr (.inl rfl))

theorem keyOff_le {R j : Nat} (hR : R ≤ 14) : 1024 ≤ VG.Proof.Aes.X86.keyOff R j ∧ VG.Proof.Aes.X86.keyOff R j ≤ lastKey := by
  simp only [VG.Proof.Aes.X86.keyOff, lastKey]; omega

theorem Ctx.arkOk {s₀ s : State} {R : Nat} {w : List Byte} (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s) {j : Nat} (hR : R ≤ 14)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R j)) : Ok VG.Proof.Aes.X86.arkCfg s :=
  Ok.of_off (r := VG.Proof.Aes.X86.reg32 (s₀.gpr sb) 2048) (r' := VG.Proof.Aes.X86.reg32 (s₀.gpr sb) 2048) (b := s₀.gpr sb)
    (b' := s₀.gpr sb) (off := 0) (off' := VG.Proof.Aes.X86.keyOff R j) (n := 2048) (n' := 2048)
    (by rw [hc.wr]; exact hp.scr) rfl hp.fit (Nat.le_refl _)
    (by show s.gpr sb = _; rw [hc.base]; simp) (by simp [VG.Proof.Aes.X86.arkCfg])
    (by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hp.scr) rfl hp.fit (Nat.le_refl _)
    hk (by simp only [VG.Proof.Aes.X86.arkCfg, VG.Proof.Aes.X86.keyOff, lastKey]; omega)
    (.inr (.inr (.inr ⟨rfl, .inl (by simp only [VG.Proof.Aes.X86.arkCfg]; have := VG.Proof.Aes.X86.keyOff_le (j := j) hR; omega)⟩)))

/-- The round keys are outside what the layers write. -/
theorem EncPre.keysAt {s₀ s : State} {R : Nat} {w : List Byte} (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s) :
    VG.Proof.Aes.X86.KeysAt s.mem (s₀.gpr sb) R w := by
  intro j hj
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  refine keyRel_congr (hp.keys j hj) fun k hk => ?_
  have := VG.Proof.Aes.X86.keyOff_le (j := j) hR
  refine hc.frame.readW (r := ⟨VG.X86.addr (s₀.gpr sb) (VG.Proof.Aes.X86.keyOff R j + 4 * k), 4⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨(s₀.gpr sb).setWidth 64, 256⟩
  rw [← VG.Proof.Aes.X86.addr_zero]
  exact VG.Proof.Aes.X86.part_disj hp.fit (by simp only [lastKey] at this; omega) (by omega)
    (.inr (by simp only [lastKey] at this; omega))

/-- The argument `rounds` is outside what the layers write. -/
theorem EncPre.arg {s₀ s : State} {R : Nat} {w : List Byte} (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s) :
    s.mem.readW (VG.X86.addr (s.gpr .esp) 8) 32 = BitVec.ofNat 32 R := by
  rw [hc.esp, ← hp.argR]
  exact hc.frame.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.argSep) (by decide)

/-! ## One layer at a time -/

/-- A layer that writes only `tmpRegs` and the first 256 bytes of the
scratch buffer keeps `Ctx`. -/
theorem layer_wp {s₀ s : State} {is : List Instr} {P : State → Prop} {Q : State → Prop}
    (hl : ∃ s', runBlock isa is s = some s' ∧ P s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧ Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem)
    (hc : VG.Proof.Aes.X86.Ctx s₀ s)
    (hQ : ∀ s', VG.Proof.Aes.X86.Ctx s₀ s' → P s' → s'.gpr kp = s.gpr kp → Q s') : WP isa (.block is) s Q := by
  obtain ⟨s', hs', hP, hrd, hwr, hoth, hfr⟩ := hl
  exact WP.of_runBlock ⟨s', hs', hQ s' (hc.step hrd hwr (fun r h _ => hoth r h) hfr) hP
    (hoth kp (by decide))⟩

theorem Q_congr {s s' : State} (hb : s'.gpr sb = s.gpr sb) (hm : s'.mem = s.mem) : VG.Proof.Aes.X86.Q s' = VG.Proof.Aes.X86.Q s := by
  funext i; simp only [VG.Proof.Aes.X86.Q, hb, hm]

/-! ## The rounds -/

/-- A middle round of the specification (round `j`). -/
def rnd (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  addRoundKey (mixColumns (shiftRows (subBytes x))) (roundKey w j)

/-- Rounds `1 … m`, as `cipher` folds them. -/
def midRounds (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => VG.Proof.Aes.X86.rnd w (j + 1) s) x

theorem midRounds_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    VG.Proof.Aes.X86.midRounds w (m + 1) x = VG.Proof.Aes.X86.rnd w (m + 1) (VG.Proof.Aes.X86.midRounds w m x) := by
  simp [VG.Proof.Aes.X86.midRounds, List.range_succ, List.foldl_append]

theorem keyOff_succ {R m : Nat} (h : m + 1 ≤ R) (hR : R ≤ 14) (B : BitVec 32) :
    B + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R m) + 32 = B + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (m + 1)) := by
  rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
  congr 2; simp only [VG.Proof.Aes.X86.keyOff, lastKey]; omega

/-- `add kp, 32`. -/
theorem addKp_wp {s₀ s : State} {Q : State → Prop} (hc : VG.Proof.Aes.X86.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.X86.Ctx s₀ s' → s'.gpr kp = s.gpr kp + 32 → Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s → Q s') :
    WP isa (.block [addI kp 32]) s Q :=
  wp_addi fun s' u => WP.block_nil (h s' (hc.upd u (.inr rfl)) u.gpr
    (VG.Proof.Aes.X86.Q_congr (u.other _ (by decide)) u.mem))

theorem sub_self_add (B : BitVec 32) (a b : Nat) :
    B + BitVec.ofNat 32 a - (B + BitVec.ofNat 32 b) = BitVec.ofNat 32 a - BitVec.ofNat 32 b := by
  bv_omega

/-- `mov eax, edi; add eax, lastKey - 32; cmp kp, eax`. -/
theorem cmpLast_wp {s₀ s : State} {Q : State → Prop} (hc : VG.Proof.Aes.X86.Ctx s₀ s) {R m : Nat}
    (hm : m + 1 < R) (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (m + 1)))
    (h : ∀ s', VG.Proof.Aes.X86.Ctx s₀ s' → s'.gpr kp = s.gpr kp → Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s →
      s'.zf = some (decide (m + 2 = R)) → Q s') :
    WP isa (.block [movR .eax .edi, addI .eax (BitVec.ofNat 32 (lastKey - 32)),
      .alu .cmp kp (.reg .eax)]) s Q := by
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_cmp fun s₃ u₃ _ hz => WP.block_nil ?_
  have c₂ := (hc.upd u₁ (.inl (by decide))).upd u₂ (.inl (by decide))
  have hk₂ : s₂.gpr kp = s.gpr kp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  refine h s₃ (c₂.step u₃.rd u₃.wr (fun r _ _ => by rw [u₃.gpr]) (by rw [u₃.mem]; exact Frame.refl _ _))
    (by rw [u₃.gpr, hk₂]) ?_ ?_
  · exact VG.Proof.Aes.X86.Q_congr ((congrFun u₃.gpr sb).trans (c₂.base.trans hc.base.symm))
      (by rw [u₃.mem, u₂.mem, u₁.mem])
  · have hb : s.gpr .edi = s₀.gpr sb := hc.base
    rw [hz, hk₂, hk, u₂.gpr, u₁.gpr, hb, VG.Proof.Aes.X86.sub_self_add, sub_beq (by simp only [VG.Proof.Aes.X86.keyOff, lastKey]; omega)
      (by simp only [lastKey]; omega)]
    simp only [VG.Proof.Aes.X86.keyOff, lastKey]
    exact congrArg some (decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩)

/-- A middle round. -/
theorem round_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R m))
    (hm : m + 1 < R) (hbs : BsRel (VG.Proof.Aes.X86.Q s) T) :
    WP isa (.block roundBody) s fun s' => VG.Proof.Aes.X86.Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (m + 1)) ∧
      BsRel (VG.Proof.Aes.X86.Q s') (fun b => VG.Proof.Aes.X86.rnd w (m + 1) (T b)) ∧ s'.zf = some (decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [roundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine VG.Proof.Aes.X86.addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, VG.Proof.Aes.X86.keyOff_succ (by omega) hR] at hk₁
  have hbs₁ : BsRel (VG.Proof.Aes.X86.Q s₁) T := by rw [hq₁]; exact hbs
  refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.sbox_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_subBytes h₂ hbs₁
  refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.shiftRows_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_shiftRows h₃ hbs₂
  refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.mixColumns_ok (hc₃.linOk hp)) hc₃ fun s₄ hc₄ h₄ hk₄ => ?_
  have hbs₄ := bs_mixColumns h₄ hbs₃
  have hk₄' : s₄.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (m + 1)) := by
    rw [hk₄, hk₃, hk₂, hk₁]
  have hkey : KeyRel (VG.Proof.Aes.X86.keyWord s₄) (roundKey w (m + 1)) := by
    have := hp.keysAt hc₄ (m + 1) (by omega)
    refine keyRel_congr this fun k _ => ?_
    simp only [VG.Proof.Aes.X86.keyWord, wordAddr, hk₄', VG.Proof.Aes.X86.addr_add]
  obtain ⟨s₅, hs₅, h₅, hrd, hwr, hoth, hfr⟩ := VG.Proof.Aes.X86.addRoundKey_ok (hc₄.arkOk hp hR hk₄')
  have hc₅ : VG.Proof.Aes.X86.Ctx s₀ s₅ := hc₄.step hrd hwr (fun r h _ => hoth r h)
    (hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by simp [VG.Proof.Aes.X86.arkCfg])⟩)
  have hbs₅ := bs_addRoundKey h₅ hbs₄ hkey
  refine WP.of_runBlock ⟨s₅, hs₅, ?_⟩
  have hk₅ : s₅.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (m + 1)) := by
    rw [hoth kp (by decide), hk₄']
  refine VG.Proof.Aes.X86.cmpLast_wp hc₅ hm hk₅ fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, by rw [hk₆, hk₅], ?_, hz₆⟩
  rw [hq₆]; exact hbs₅

/-- `esi :=` the first round key. -/
theorem keyStart_wp {s₀ s : State} {R : Nat} {w : List Byte} (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s)
    {Q : State → Prop}
    (h : ∀ s', VG.Proof.Aes.X86.Ctx s₀ s' → s'.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R 0) →
      Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s → Q s') :
    WP isa (.block keyStart) s Q := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esp) 8) 4 := by
    rw [hc.rd, hc.wr, hc.esp]; exact hp.argIn
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ _ => wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ =>
    wp_add fun s₆ u₆ _ => wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_sub fun s₉ u₉ _ =>
    wp_mov fun s₁₀ u₁₀ => WP.block_nil ?_
  have c : VG.Proof.Aes.X86.Ctx s₀ s₁₀ := ((((((((((hc.upd u₁ (.inr rfl)).upd u₂ (.inr rfl)).upd u₃ (.inr rfl)).upd u₄
    (.inr rfl)).upd u₅ (.inr rfl)).upd u₆ (.inr rfl)).upd u₇ (.inl (by decide))).upd u₈
    (.inl (by decide))).upd u₉ (.inl (by decide))).upd u₁₀ (.inr rfl))
  refine h s₁₀ c ?_ (VG.Proof.Aes.X86.Q_congr (by rw [c.base, hc.base])
    (by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]))
  have e6 : s₆.gpr .esi = BitVec.ofNat 32 (32 * R) := by
    rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hp.arg hc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e7 : s₇.gpr .eax = s₀.gpr sb := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ← hc.base]; rfl
  show s₁₀.gpr .esi = _
  rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₈.other .esi (by decide), u₇.other .esi (by decide), e6, e7]
  simp only [VG.Proof.Aes.X86.keyOff, lastKey, Nat.sub_zero]
  bv_omega

theorem ark_step {s₀ s : State} {R j : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s) (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R j))
    (hj : j ≤ R) (hbs : BsRel (VG.Proof.Aes.X86.Q s) T) {P : State → Prop}
    (h : ∀ s', VG.Proof.Aes.X86.Ctx s₀ s' → s'.gpr kp = s.gpr kp →
      BsRel (VG.Proof.Aes.X86.Q s') (fun b => addRoundKey (T b) (roundKey w j)) → P s') :
    WP isa (.block addRoundKey) s P := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hkey : KeyRel (VG.Proof.Aes.X86.keyWord s) (roundKey w j) := by
    refine keyRel_congr (hp.keysAt hc j hj) fun k _ => ?_
    simp only [VG.Proof.Aes.X86.keyWord, wordAddr, hk, VG.Proof.Aes.X86.addr_add]
  obtain ⟨s', hs', h', hrd, hwr, hoth, hfr⟩ := VG.Proof.Aes.X86.addRoundKey_ok (hc.arkOk hp hR hk)
  have hc' : VG.Proof.Aes.X86.Ctx s₀ s' := hc.step hrd hwr (fun r h _ => hoth r h)
    (hfr.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by simp [VG.Proof.Aes.X86.arkCfg])⟩)
  exact WP.of_runBlock ⟨s', hs', h s' hc' (hoth kp (by decide)) (bs_addRoundKey h' hbs hkey)⟩

theorem cipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher R w x = addRoundKey (shiftRows (subBytes (VG.Proof.Aes.X86.midRounds w (R - 1)
      (addRoundKey x (roundKey w 0))))) (roundKey w R) := rfl

/-- Two blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hin : InRel (VG.Proof.Aes.X86.Q s₀) S) :
    WP isa encrypt2 s₀ fun s => VG.Proof.Aes.X86.Ctx s₀ s ∧ InRel (VG.Proof.Aes.X86.Q s) (fun b => cipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w 0)
  -- The rounds done so far.
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ VG.Proof.Aes.X86.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R m) ∧ BsRel (VG.Proof.Aes.X86.Q s) (fun b => VG.Proof.Aes.X86.midRounds w m (A b))
  let Mid : State → Prop := fun s => VG.Proof.Aes.X86.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (R - 1)) ∧
    BsRel (VG.Proof.Aes.X86.Q s) (fun b => VG.Proof.Aes.X86.midRounds w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- ortho, the first round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.toBs_ok ((Ctx.refl s₀).linOk hp)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine VG.Proof.Aes.X86.keyStart_wp hp hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (VG.Proof.Aes.X86.Q s₂) S := by rw [hq₂]; exact hbs₁
    exact VG.Proof.Aes.X86.ark_step hp hc₂ hk₂ (by omega) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (VG.Proof.Aes.X86.round_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨by simp [X86.eval, hz, hlast], hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [VG.Proof.Aes.X86.midRounds_succ]
    · refine .inr ⟨by simp [X86.eval, hz, hlast], R - 1 - (m + 1), by omega, m + 1, rfl, by omega, hc', hk',
        fun b hb i hi => by rw [hbs' b hb i hi]; simp only [VG.Proof.Aes.X86.midRounds_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [lastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.X86.addKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, VG.Proof.Aes.X86.keyOff_succ (by omega) hR, show R - 1 + 1 = R by omega] at hk₁
    have hbs₁ : BsRel (VG.Proof.Aes.X86.Q s₁) (fun b => VG.Proof.Aes.X86.midRounds w (R - 1) (A b)) := by rw [hq₁]; exact hbs
    refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.sbox_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_subBytes h₂ hbs₁
    refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.shiftRows_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_shiftRows h₃ hbs₂
    refine VG.Proof.Aes.X86.ark_step hp hc₃ (by rw [hk₃, hk₂, hk₁]) (Nat.le_refl R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.fromBs_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [VG.Proof.Aes.X86.cipher_eq]; rfl

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Keys`. -/
section

/-!
# Bitslicing the round keys, on x86 (32-bit)

The key loop of `vg_aes_ctr32` bitslices each round key (loaded as two
identical blocks) with `ortho` and stores it in the scratch buffer. The
loads and stores are checked by evaluation over the naming domain
(`Bitslice.names`), `ortho` by its proof (`Linear.lean`), and the address
computations by symbolic execution.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (roundKey)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_bswap wp_ldm wp_xorm wp_stm sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-! ## Loading a round key -/

/-- The loads and stores of `keyLoad`, after the address. -/
def loadMoves : List Instr :=
  (List.range 4).flatMap fun w => [.mov .ebx (.mem (at_ .eax (4 * w))), st (2 * w) .ebx, st (2 * w + 1) .ebx]

theorem keyLoad_eq : keyLoad = ([movR .eax .esi, addR .eax .eax, addR .eax .eax, addR .eax .eax,
    addR .eax .eax, .mov .ebx (.mem (argOp 0)), addR .eax .ebx] : List Instr) ++ VG.Proof.Aes.X86.loadMoves := rfl

def loadCfg : Cfg := { base := sb, slots := 8, ext := .eax, exts := 4 }

def loadPost (e : Env Nat) : Bool :=
  (List.range 4).all fun w => e.slot (2 * w) == some w && e.slot (2 * w + 1) == some w

theorem loadMoves_check :
    VG.X86.Straight.check (names 32) VG.Proof.Aes.X86.loadCfg (fun k => some k) VG.Proof.Aes.X86.loadMoves { reg := fun _ => none, slot := fun _ => none }
      VG.Proof.Aes.X86.loadPost = true := by
  decide +kernel

theorem loadMoves_ok {s : State} (hok : Ok VG.Proof.Aes.X86.loadCfg s) :
    ∃ s', runBlock isa VG.Proof.Aes.X86.loadMoves s = some s' ∧
      (∀ w < 4, VG.Proof.Aes.X86.Q s' (2 * w) = s.mem.readW (wordAddr (s.gpr .eax) w) 32 ∧
        VG.Proof.Aes.X86.Q s' (2 * w + 1) = s.mem.readW (wordAddr (s.gpr .eax) w) 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.loadCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.X86.loadMoves_check
  let V : Nat → BitVec 32 := fun k => s.mem.readW (wordAddr (s.gpr .eax) k) 32
  have hrel : Rel (NameRel V) VG.Proof.Aes.X86.loadCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  have hb : s'.gpr sb = s.gpr sb := p.base
  refine ⟨s', hs', fun w hw => ?_, p.rd, p.wr, fun r hr => p.other r ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost w (List.mem_range.mpr hw)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    have h1 := p.rel.slot _ _ (by simp [VG.Proof.Aes.X86.loadCfg]; omega) this.1
    have h2 := p.rel.slot _ _ (by simp [VG.Proof.Aes.X86.loadCfg]; omega) this.2
    simp only [NameRel, VG.Proof.Aes.X86.loadCfg, hb] at h1 h2
    exact ⟨by simp only [VG.Proof.Aes.X86.Q, hb]; exact h1, by simp only [VG.Proof.Aes.X86.Q, hb]; exact h2⟩
  · have : (loadMoves.all fun i => i.dst != some r) = true := by
      revert hr; cases r <;> decide
    simp [this]

/-! ## Storing it -/

/-- The loads and stores of `keyStore`, after the address. -/
def storeMoves : List Instr := (List.range 8).flatMap fun k => [movS .eax k, .store (at_ .ebx (4 * k)) .eax]

theorem keyStore_eq : keyStore = ([.mov .eax (.mem (argOp 1)), subR .eax .esi, addR .eax .eax,
    addR .eax .eax, addR .eax .eax, addR .eax .eax, addR .eax .eax, movR .ebx .edi,
    addI .ebx (BitVec.ofNat 32 lastKey), subR .ebx .eax] : List Instr) ++ VG.Proof.Aes.X86.storeMoves := rfl

def storeCfg : Cfg := { base := .ebx, slots := 8, ext := sb, exts := 8 }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem storeMoves_check :
    VG.X86.Straight.check (names 32) VG.Proof.Aes.X86.storeCfg (fun k => some k) VG.Proof.Aes.X86.storeMoves { reg := fun _ => none, slot := fun _ => none }
      VG.Proof.Aes.X86.storePost = true := by
  decide +kernel

theorem storeMoves_ok {s : State} (hok : Ok VG.Proof.Aes.X86.storeCfg s) :
    ∃ s', runBlock isa VG.Proof.Aes.X86.storeMoves s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr .ebx) k) 32 = VG.Proof.Aes.X86.Q s k) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.storeCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.X86.storeMoves_check
  let V : Nat → BitVec 32 := fun k => VG.Proof.Aes.X86.Q s k
  have hrel : Rel (NameRel V) VG.Proof.Aes.X86.storeCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  have hb : s'.gpr .ebx = s.gpr .ebx := p.base
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, fun r hr => p.other r ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot k k (by simp [VG.Proof.Aes.X86.storeCfg]; omega) this
    simp only [NameRel, VG.Proof.Aes.X86.storeCfg, hb] at h
    exact h
  · have : (storeMoves.all fun i => i.dst != some r) = true := by
      revert hr; cases r <;> decide
    simp [this]

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `B`, the key schedule `w`
at `S` (as the bytes there), `rounds` and the schedule pointer the
arguments. -/
structure KSetup (s₀ : State) (B S : BitVec 32) (R : Nat) (w : List Byte) : Prop where
  scr : VG.Proof.Aes.X86.reg32 B 2048 ∈ s₀.wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  sch : VG.Proof.Aes.X86.reg32 S 240 ∈ s₀.rd ++ s₀.wr
  fitS : S.toNat + 240 ≤ 2 ^ 32
  sep : (VG.Proof.Aes.X86.reg32 S 240).Disjoint (VG.Proof.Aes.X86.reg32 B 2048)
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  base : s₀.gpr sb = B
  argIn : ∀ i < 2, InRegions (s₀.rd ++ s₀.wr) (VG.X86.addr (s₀.gpr .esp) (4 + 4 * i)) 4
  arg0 : s₀.mem.readW (VG.X86.addr (s₀.gpr .esp) 4) 32 = S
  arg1 : s₀.mem.readW (VG.X86.addr (s₀.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  argSep : ∀ i < 2, Region.Disjoint ⟨VG.X86.addr (s₀.gpr .esp) (4 + 4 * i), 4⟩ (VG.Proof.Aes.X86.reg32 B 2048)
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (VG.X86.addr S i)

/-- The regions the key loop writes. -/
abbrev keyFrame (B : BitVec 32) : List Region := [VG.Proof.Aes.X86.reg32 B 256, ⟨VG.X86.addr B 1024, 480⟩]

/-- The bitsliced round key `i` is in the scratch buffer. -/
def KeyAt (m : Mem) (B : BitVec 32) (R : Nat) (w : List Byte) (i : Nat) : Prop :=
  KeyRel (fun k => m.readW (VG.X86.addr B (VG.Proof.Aes.X86.keyOff R i + 4 * k)) 32) (roundKey w i)

/-- Before bitslicing round key `j`. -/
structure KInv (s₀ : State) (B : BitVec 32) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  esi : s.gpr .esi = BitVec.ofNat 32 j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ tmpRegs → r ≠ .esi → s.gpr r = s₀.gpr r
  frame : Frame (VG.Proof.Aes.X86.keyFrame B) s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R → VG.Proof.Aes.X86.KeyAt s.mem B R w i

/-- After the loop. -/
structure KDone (s₀ : State) (B : BitVec 32) (R : Nat) (w : List Byte) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ tmpRegs → r ≠ .esi → s.gpr r = s₀.gpr r
  frame : Frame (VG.Proof.Aes.X86.keyFrame B) s₀.mem s.mem
  keys : VG.Proof.Aes.X86.KeysAt s.mem B R w

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 32} {w : List Byte} {j : Nat}
    (h : BsRel K fun _ => VG.Proof.Aes.X86.rkv w j) : KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, getD_eq _ hi, VG.Proof.Aes.X86.rkv, Vector.getElem_ofFn]

section
variable {s₀ : State} {B S : BitVec 32} {R : Nat} {w : List Byte} (hk : VG.Proof.Aes.X86.KSetup s₀ B S R w)
include hk

theorem KSetup.hR : R ≤ 14 := by rcases hk.rounds with h | h | h <;> omega

/-- The key frame is within the scratch buffer, and so apart from the schedule and the arguments. -/
theorem KSetup.frame_sub : ∀ r ∈ VG.Proof.Aes.X86.keyFrame B, Region.Sub r (VG.Proof.Aes.X86.reg32 B 2048) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Region.sub_prefix (by omega)
  · exact VG.Proof.Aes.X86.part_sub_reg hk.fitB (by omega)

theorem KSetup.arg {s : State} (hf : Frame (VG.Proof.Aes.X86.keyFrame B) s₀.mem s.mem) {i : Nat} (hi : i < 2) :
    s.mem.readW (VG.X86.addr (s₀.gpr .esp) (4 + 4 * i)) 32 = s₀.mem.readW (VG.X86.addr (s₀.gpr .esp) (4 + 4 * i)) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => (hk.argSep i hi).sub_right (hk.frame_sub r hr))
    (by decide)

theorem KSetup.sched {s : State} (hf : Frame (VG.Proof.Aes.X86.keyFrame B) s₀.mem s.mem) {i : Nat} (hi : i < 240) :
    s.mem (VG.X86.addr S i) = s₀.mem (VG.X86.addr S i) :=
  hf _ fun r hr hc => hk.sep _ (VG.Proof.Aes.X86.reg_contains hk.fitS (by omega) (by decide))
    (hk.frame_sub r hr _ hc)

theorem KSetup.linOk {s : State} (hb : s.gpr sb = B) (hwr : s.wr = s₀.wr) (hrd : s.rd = s₀.rd) :
    Ok VG.Proof.Aes.X86.linCfg s :=
  Ok.of_off (r := VG.Proof.Aes.X86.reg32 B 2048) (r' := VG.Proof.Aes.X86.reg32 B 2048) (b := B) (b' := B) (off := 0) (off' := 0)
    (n := 2048) (n' := 2048) (by rw [hwr]; exact hk.scr) rfl hk.fitB (Nat.le_refl _)
    (by show s.gpr sb = _; rw [hb]; simp) (by simp [VG.Proof.Aes.X86.linCfg])
    (by rw [hrd, hwr]; exact List.mem_append_right _ hk.scr) rfl hk.fitB (Nat.le_refl _)
    (by show s.gpr sb = _; rw [hb]; simp) (by simp [VG.Proof.Aes.X86.linCfg]) (.inr (.inl rfl))

theorem keyBody_ok {j : Nat} {s : State} (hi : VG.Proof.Aes.X86.KInv s₀ B R w j s) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ s'.cf = some true ∧ VG.Proof.Aes.X86.KDone s₀ B R w s') ∨
      (0 < j ∧ s'.cf = some false ∧ VG.Proof.Aes.X86.KInv s₀ B R w (j - 1) s') := by
  have hR := hk.hR
  have hjR := hi.hj
  have hsb : s.gpr sb = B := by rw [hi.keep sb (by decide) (by decide), hk.base]
  have hesp : s.gpr .esp = s₀.gpr .esp := hi.keep _ (by decide) (by decide)
  have harg : ∀ i < 2, InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esp) (4 + 4 * i)) 4 := fun i hi' => by
    rw [hi.rd, hi.wr, hesp]; exact hk.argIn i hi'
  simp only [keyBody]
  repeat rw [WP.block_append_iff (M := isa)]
  -- The address of the round key.
  rw [VG.Proof.Aes.X86.keyLoad_eq, WP.block_append_iff (M := isa)]
  refine wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ _ => wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ =>
    wp_add fun s₅ u₅ _ => wp_ldm (B := s.gpr .esp) (o := 4) (by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)]) (by
      rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact harg 0 (by omega))
    fun s₅' u₅' => wp_add fun s₆ u₆ _ => WP.block_nil ?_
  have hm₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅'.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g₆ : ∀ r, r ≠ .eax → r ≠ .ebx → s₆.gpr r = s.gpr r := fun r hr hr' => by
    rw [u₆.other r hr, u₅'.other r hr', u₅.other r hr, u₄.other r hr, u₃.other r hr, u₂.other r hr,
      u₁.other r hr]
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅'.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅'.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have a0 : s.mem.readW (VG.X86.addr (s.gpr .esp) 4) 32 = S := by
    have := hk.arg hi.frame (i := 0) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [hesp, this, hk.arg0]
  have heax : s₆.gpr .eax = S + BitVec.ofNat 32 (16 * j) := by
    rw [u₆.gpr, u₅'.gpr, u₅'.other .eax (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hi.esi,
      u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, a0, BitVec.add_comm _ S]
    congr 1
    bv_omega
  -- The loads.
  have hok₁ : Ok VG.Proof.Aes.X86.loadCfg s₆ :=
    Ok.of_off (r := VG.Proof.Aes.X86.reg32 B 2048) (r' := VG.Proof.Aes.X86.reg32 S 240) (b := B) (b' := S) (off := 0) (off' := 16 * j)
      (n := 2048) (n' := 240) (by rw [wr₆, hi.wr]; exact hk.scr) rfl hk.fitB (Nat.le_refl _)
      (by show s₆.gpr sb = _; rw [g₆ _ (by decide) (by decide), hsb]; simp) (by simp [VG.Proof.Aes.X86.loadCfg])
      (by rw [rd₆, wr₆, hi.rd, hi.wr]; exact hk.sch) rfl hk.fitS (Nat.le_refl _) heax
      (by simp only [VG.Proof.Aes.X86.loadCfg]; omega) (.inr (.inr (.inl hk.sep.symm)))
  obtain ⟨s₇, hs₇, hq₇, hrd₇, hwr₇, hoth₇, hfr₇⟩ := VG.Proof.Aes.X86.loadMoves_ok hok₁
  refine WP.of_runBlock ⟨s₇, hs₇, ?_⟩
  have hin : InRel (VG.Proof.Aes.X86.Q s₇) fun _ => VG.Proof.Aes.X86.rkv w j := by
    intro bb hb i hi16 t ht
    rw [getD_eq _ hi16, VG.Proof.Aes.X86.rkv, Vector.getElem_ofFn, VG.Proof.Aes.X86.roundKey_getD hi16, hk.w _ (by omega)]
    have hq := hq₇ (i / 4) (by omega)
    have e : bb + 2 * (i / 4) = if bb = 0 then 2 * (i / 4) else 2 * (i / 4) + 1 := by split <;> omega
    rw [e]
    have hw : VG.Proof.Aes.X86.Q s₇ (if bb = 0 then 2 * (i / 4) else 2 * (i / 4) + 1) =
        s₆.mem.readW (wordAddr (s₆.gpr .eax) (i / 4)) 32 := by split <;> simp [hq]
    rw [hw, VG.Proof.Aes.X86.readW_bit _ _ (by omega) ht, hm₆, heax, wordAddr, VG.Proof.Aes.X86.addr_add,
      VG.Proof.Aes.X86.addr_add64 (by have := hk.fitS; omega),
      show 16 * j + 4 * (i / 4) + i % 4 = 16 * j + i by omega,
      hk.sched hi.frame (by omega)]
  -- Bitslice it.
  have hsb₇ : s₇.gpr sb = B := by rw [hoth₇ _ (by decide), g₆ _ (by decide) (by decide), hsb]
  obtain ⟨s₈, hs₈, hq₈, hrd₈, hwr₈, hoth₈, hfr₈⟩ :=
    VG.Proof.Aes.X86.toBs_ok (hk.linOk hsb₇ (by rw [hwr₇, wr₆, hi.wr]) (by rw [hrd₇, rd₆, hi.rd]))
  refine WP.of_runBlock ⟨s₈, hs₈, ?_⟩
  have hbs₈ := bs_of_in hq₈ hin
  have hsb₈ : s₈.gpr sb = B := by rw [hoth₈ _ (by decide), hsb₇]
  have hesi₈ : s₈.gpr .esi = BitVec.ofNat 32 j := by
    rw [hoth₈ _ (by decide), hoth₇ _ (by decide), g₆ _ (by decide) (by decide), hi.esi]
  have hesp₈ : s₈.gpr .esp = s₀.gpr .esp := by
    rw [hoth₈ _ (by decide), hoth₇ _ (by decide), g₆ _ (by decide) (by decide), hesp]
  -- The memory so far.
  have fr₈' : Frame [VG.Proof.Aes.X86.reg32 B 256] s.mem s₈.mem := by
    rw [← hm₆]
    refine (hfr₇.sub fun r hr => ⟨VG.Proof.Aes.X86.reg32 B 256, List.mem_cons_self .., ?_⟩).trans
      (hfr₈.sub fun r hr => ⟨VG.Proof.Aes.X86.reg32 B 256, List.mem_cons_self .., ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, VG.Proof.Aes.X86.loadCfg, g₆ _ (show sb ≠ .eax by decide) (by decide), hsb]
      exact Region.sub_prefix (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, VG.Proof.Aes.X86.linCfg, hsb₇]
      exact Region.sub_prefix (by omega)
  have fr₈ : Frame (VG.Proof.Aes.X86.keyFrame B) s₀.mem s₈.mem :=
    hi.frame.trans (fr₈'.sub fun r hr => ⟨VG.Proof.Aes.X86.reg32 B 256, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  -- The address to store it at.
  rw [VG.Proof.Aes.X86.keyStore_eq, WP.block_append_iff (M := isa)]
  have hin₈ : InRegions (s₈.rd ++ s₈.wr) (VG.X86.addr (s₀.gpr .esp) 8) 4 := by
    rw [hrd₈, hwr₈, hrd₇, hwr₇, rd₆, wr₆, hi.rd, hi.wr]; exact hk.argIn 1 (by omega)
  refine wp_ldm (B := s₀.gpr .esp) (o := 8) hesp₈ hin₈ fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ _ =>
    wp_add fun s₁₁ u₁₁ _ => wp_add fun s₁₂ u₁₂ _ => wp_add fun s₁₃ u₁₃ _ => wp_add fun s₁₄ u₁₄ _ =>
    wp_add fun s₁₅ u₁₅ _ => wp_mov fun s₁₆ u₁₆ => wp_addi fun s₁₇ u₁₇ => wp_sub fun s₁₈ u₁₈ _ =>
    WP.block_nil ?_
  have a1 : s₈.mem.readW (VG.X86.addr (s₀.gpr .esp) 8) 32 = BitVec.ofNat 32 R := by
    have := hk.arg fr₈ (i := 1) (by omega)
    simp only [Nat.mul_one] at this
    rw [this, hk.arg1]
  have heax : s₁₅.gpr .eax = BitVec.ofNat 32 (32 * (R - j)) := by
    rw [u₁₅.gpr, u₁₄.gpr, u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other .esi (by decide),
      hesi₈, a1]
    bv_omega
  have hebx : s₁₈.gpr .ebx = B + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R j) := by
    rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, u₁₇.other .eax (by decide), u₁₆.other .eax (by decide), heax]
    have : s₁₅.gpr .edi = B := by
      rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
        u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
        u₉.other _ (by decide)]; exact hsb₈
    rw [this]
    simp only [VG.Proof.Aes.X86.keyOff, lastKey]
    bv_omega
  have hm₁₈ : s₁₈.mem = s₈.mem := by
    rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have hrd₁₈ : s₁₈.rd = s₀.rd := by
    rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, hrd₈, hrd₇,
      rd₆, hi.rd]
  have hwr₁₈ : s₁₈.wr = s₀.wr := by
    rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, hwr₈, hwr₇,
      wr₆, hi.wr]
  have g₁₈ : ∀ r, r ≠ .eax → r ≠ .ebx → s₁₈.gpr r = s₈.gpr r := fun r h1 h2 => by
    rw [u₁₈.other r h2, u₁₇.other r h2, u₁₆.other r h2, u₁₅.other r h1, u₁₄.other r h1,
      u₁₃.other r h1, u₁₂.other r h1, u₁₁.other r h1, u₁₀.other r h1, u₉.other r h1]
  have hko := VG.Proof.Aes.X86.keyOff_le (j := j) hR
  have hok₂ : Ok VG.Proof.Aes.X86.storeCfg s₁₈ :=
    Ok.of_off (r := VG.Proof.Aes.X86.reg32 B 2048) (r' := VG.Proof.Aes.X86.reg32 B 2048) (b := B) (b' := B) (off := VG.Proof.Aes.X86.keyOff R j)
      (off' := 0) (n := 2048) (n' := 2048) (by rw [hwr₁₈]; exact hk.scr) rfl hk.fitB (Nat.le_refl _)
      hebx (by simp only [VG.Proof.Aes.X86.storeCfg, lastKey] at hko ⊢; omega)
      (by rw [hrd₁₈, hwr₁₈]; exact List.mem_append_right _ hk.scr) rfl hk.fitB (Nat.le_refl _)
      (by show s₁₈.gpr sb = _; rw [g₁₈ _ (by decide) (by decide), hsb₈]; simp)
      (by simp only [VG.Proof.Aes.X86.storeCfg]; omega)
      (.inr (.inr (.inr ⟨rfl, .inr (by simp only [VG.Proof.Aes.X86.storeCfg]; omega)⟩)))
  obtain ⟨s₁₉, hs₁₉, hst₁₉, hrd₁₉, hwr₁₉, hoth₁₉, hfr₁₉⟩ := VG.Proof.Aes.X86.storeMoves_ok hok₂
  refine WP.of_runBlock ⟨s₁₉, hs₁₉, ?_⟩
  refine wp_subi fun s₂₀ u₂₀ hcf _ => WP.block_nil ?_
  -- What is kept.
  have hkeep : ∀ r, r ∉ tmpRegs → r ≠ .esi → s₂₀.gpr r = s₀.gpr r := by
    intro r hr hne
    have h1 : r ≠ .eax := by rintro rfl; exact hr (by decide)
    have h2 : r ≠ .ebx := by rintro rfl; exact hr (by decide)
    rw [u₂₀.other r hne, hoth₁₉ r h1, g₁₈ r h1 h2, hoth₈ r hr, hoth₇ r h2, g₆ r h1 h2, hi.keep r hr hne]
  have hebx' : s₁₈.gpr .ebx = B + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R j) := hebx
  have hstore : slotRegion VG.Proof.Aes.X86.storeCfg s₁₈ = ⟨VG.X86.addr B (VG.Proof.Aes.X86.keyOff R j), 32⟩ := by
    simp only [slotRegion, VG.Proof.Aes.X86.storeCfg]; rw [show s₁₈.gpr .ebx = _ from hebx']; rfl
  have hm₂₀ : s₂₀.mem = s₁₉.mem := u₂₀.mem
  have fr : Frame (VG.Proof.Aes.X86.keyFrame B) s₀.mem s₂₀.mem := by
    rw [hm₂₀]
    refine fr₈.trans ?_
    rw [← hm₁₈]
    refine hfr₁₉.sub fun r hr => ⟨⟨VG.X86.addr B 1024, 480⟩, by simp, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hstore]
    exact VG.Proof.Aes.X86.part_sub hk.fitB (by omega) (by simp only [lastKey] at hko; omega)
      (by simp only [lastKey] at hko; omega)
  -- The keys stored before.
  have hold : ∀ i, j < i → i ≤ R → VG.Proof.Aes.X86.KeyAt s₂₀.mem B R w i := by
    intro i hji hiR
    refine keyRel_congr (hi.done i hji hiR) fun k hk8 => ?_
    have hki := VG.Proof.Aes.X86.keyOff_le (j := i) hR
    rw [hm₂₀, hfr₁₉.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hstore]
        exact VG.Proof.Aes.X86.part_disj hk.fitB (by simp only [lastKey] at hki; omega)
          (by simp only [lastKey] at hko; omega)
          (by simp only [VG.Proof.Aes.X86.keyOff, lastKey] at hki hko ⊢; omega)) (by decide), hm₁₈]
    refine fr₈'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
    rw [← VG.Proof.Aes.X86.addr_zero]
    exact VG.Proof.Aes.X86.part_disj hk.fitB (by simp only [lastKey] at hki; omega) (by omega)
      (.inr (by simp only [lastKey] at hki; omega))
  -- The key stored now.
  have hnew : VG.Proof.Aes.X86.KeyAt s₂₀.mem B R w j := by
    refine keyRel_congr (VG.Proof.Aes.X86.keyRel_of_bs hbs₈) fun k hk8 => ?_
    have := hst₁₉ k hk8
    rw [hebx', wordAddr, VG.Proof.Aes.X86.addr_add, VG.Proof.Aes.X86.Q_congr (g₁₈ _ (by decide) (by decide)) hm₁₈] at this
    rw [hm₂₀, this]
  have hesi : s₁₉.gpr .esi = BitVec.ofNat 32 j := by
    rw [hoth₁₉ _ (by decide), g₁₈ _ (by decide) (by decide), hesi₈]
  rw [hesi, toNat_ofNat_lt (by omega)] at hcf
  have hrd : s₂₀.rd = s₀.rd := by rw [u₂₀.rd, hrd₁₉, hrd₁₈]
  have hwr : s₂₀.wr = s₀.wr := by rw [u₂₀.wr, hwr₁₉, hwr₁₈]
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, by simpa using hcf, ⟨hrd, hwr, hkeep, fr, fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega) hiR
  · refine .inr ⟨by omega, by simpa [h0] using hcf, ⟨by omega, ?_, hrd, hwr, hkeep, fr, ?_⟩⟩
    · rw [u₂₀.gpr, hesi]; exact ofNat_pred (by omega)
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega) hiR

theorem keyLoop_ok {s : State} (hi : VG.Proof.Aes.X86.KInv s₀ B R w R s) :
    WP isa (.loop (.block keyBody) .ae) s (VG.Proof.Aes.X86.KDone s₀ B R w) := by
  refine WP.loop (M := isa) (VG.Proof.Aes.X86.KInv s₀ B R w) (fun n s hs => ?_) R s hi
  refine WP.mono (VG.Proof.Aes.X86.keyBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hcf, hd⟩ | ⟨hn, hcf, hi'⟩
  · exact .inl ⟨by simp [X86.eval, hcf], hd⟩
  · exact .inr ⟨by simp [X86.eval, hcf], n - 1, by omega, hi'⟩

end

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Group`. -/
section

/-!
# One group of counter-mode blocks on x86 (32-bit)

`ctrBlocks` builds the counter blocks `c` and `c + 1` from the words of the
counter block in the scratch buffer (`ctrBlocks_wp`, then `ctr_inRel` for
`InRel`), `encrypt2` encrypts them (`Encrypt.lean`), and `xorGroup` XORs the
keystream into the data, a word at a time.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_bswap wp_ldm wp_xorm wp_stm sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-! ## Words of the scratch buffer -/

/-! ## The counter blocks -/

/-- The words of the counter block in the scratch buffer at `B`. -/
abbrev cw (m : Mem) (B : BitVec 32) (w : Nat) : BitVec 32 := m.readW (VG.X86.addr B (cwOff w)) 32
abbrev cnum (m : Mem) (B : BitVec 32) : BitVec 32 := m.readW (VG.X86.addr B cNum) 32

/-- What `ctrBlocks` leaves in slot `k`. -/
def ctrSlot (m : Mem) (B : BitVec 32) (k : Nat) : BitVec 32 :=
  if k < 6 then VG.Proof.Aes.X86.cw m B (k / 2) else bswap (VG.Proof.Aes.X86.cnum m B + BitVec.ofNat 32 (k - 6))

theorem ctrBlocks_eq : ctrBlocks = ([
    .mov .eax (.mem (at_ .edi 272)), .store (at_ .edi 0) .eax,
    .mov .eax (.mem (at_ .edi 276)), .store (at_ .edi 8) .eax,
    .mov .eax (.mem (at_ .edi 280)), .store (at_ .edi 16) .eax,
    .mov .eax (.mem (at_ .edi 284)), .alu .add .eax (.imm 0), .bswap .eax, .store (at_ .edi 24) .eax,
    .mov .eax (.mem (at_ .edi 272)), .store (at_ .edi 4) .eax,
    .mov .eax (.mem (at_ .edi 276)), .store (at_ .edi 12) .eax,
    .mov .eax (.mem (at_ .edi 280)), .store (at_ .edi 20) .eax,
    .mov .eax (.mem (at_ .edi 284)), .alu .add .eax (.imm 1), .bswap .eax, .store (at_ .edi 28) .eax,
    .mov .eax (.mem (at_ .edi 284)), .alu .add .eax (.imm 2), .store (at_ .edi 284) .eax] :
    List Instr) := rfl

/-- The two counter blocks. -/
theorem ctrBlocks_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hfit : B.toNat + 2048 ≤ 2 ^ 32)
    (hw : VG.Proof.Aes.X86.reg32 B 2048 ∈ s.wr) {P : State → Prop}
    (h : ∀ s', (∀ k < 8, VG.Proof.Aes.X86.Q s' k = VG.Proof.Aes.X86.ctrSlot s.mem B k) → VG.Proof.Aes.X86.cnum s'.mem B = VG.Proof.Aes.X86.cnum s.mem B + 2 →
      Frame [VG.Proof.Aes.X86.reg32 B 32, ⟨VG.X86.addr B cNum, 4⟩] s.mem s'.mem →
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block ctrBlocks) s P := by
  rw [VG.Proof.Aes.X86.ctrBlocks_eq]
  have hin : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (VG.X86.addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact VG.Proof.Aes.X86.in_reg hw hfit ho (by decide)
  have hrd : ∀ (t : State), t.rd = s.rd → t.wr = s.wr → ∀ o, o + 4 ≤ 2048 →
      InRegions (t.rd ++ t.wr) (VG.X86.addr B o) 4 :=
    fun t h1 h2 o ho => VG.Proof.Aes.X86.in_rd (hin t h2 o ho)
  refine wp_ldm hb (hrd _ rfl rfl 272 (by omega)) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .edi = B := (u₁.other _ (by decide)).trans hb
  refine wp_stm b₁ (hin _ u₁.wr 0 (by omega)) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .edi = B := by rw [u₂.gpr]; exact b₁
  refine wp_ldm b₂ (hrd _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 276 (by omega)) fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .edi = B := (u₃.other _ (by decide)).trans b₂
  refine wp_stm b₃ (hin _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 8 (by omega)) fun s₄ u₄ => ?_
  have b₄ : s₄.gpr .edi = B := by rw [u₄.gpr]; exact b₃
  refine wp_ldm b₄ (hrd _ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    280 (by omega)) fun s₅ u₅ => ?_
  have b₅ : s₅.gpr .edi = B := (u₅.other _ (by decide)).trans b₄
  refine wp_stm b₅ (hin _ (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 16 (by omega)) fun s₆ u₆ => ?_
  have b₆ : s₆.gpr .edi = B := by rw [u₆.gpr]; exact b₅
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_ldm b₆ (hrd _ rd₆ wr₆ 284 (by omega)) fun s₇ u₇ => ?_
  refine wp_addi fun s₈ u₈ => wp_bswap fun s₉ u₉ => ?_
  have b₉ : s₉.gpr .edi = B := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide)]; exact b₆
  have rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, rd₆]
  have wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, wr₆]
  refine wp_stm b₉ (hin _ wr₉ 24 (by omega)) fun s₁₀ u₁₀ => ?_
  have b₁₀ : s₁₀.gpr .edi = B := by rw [u₁₀.gpr]; exact b₉
  refine wp_ldm b₁₀ (hrd _ (by rw [u₁₀.rd, rd₉]) (by rw [u₁₀.wr, wr₉]) 272 (by omega)) fun s₁₁ u₁₁ => ?_
  have b₁₁ : s₁₁.gpr .edi = B := (u₁₁.other _ (by decide)).trans b₁₀
  refine wp_stm b₁₁ (hin _ (by rw [u₁₁.wr, u₁₀.wr, wr₉]) 4 (by omega)) fun s₁₂ u₁₂ => ?_
  have b₁₂ : s₁₂.gpr .edi = B := by rw [u₁₂.gpr]; exact b₁₁
  have rd₁₂ : s₁₂.rd = s.rd := by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, rd₉]
  have wr₁₂ : s₁₂.wr = s.wr := by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉]
  refine wp_ldm b₁₂ (hrd _ rd₁₂ wr₁₂ 276 (by omega)) fun s₁₃ u₁₃ => ?_
  have b₁₃ : s₁₃.gpr .edi = B := (u₁₃.other _ (by decide)).trans b₁₂
  refine wp_stm b₁₃ (hin _ (by rw [u₁₃.wr, wr₁₂]) 12 (by omega)) fun s₁₄ u₁₄ => ?_
  have b₁₄ : s₁₄.gpr .edi = B := by rw [u₁₄.gpr]; exact b₁₃
  refine wp_ldm b₁₄ (hrd _ (by rw [u₁₄.rd, u₁₃.rd, rd₁₂]) (by rw [u₁₄.wr, u₁₃.wr, wr₁₂]) 280 (by omega))
    fun s₁₅ u₁₅ => ?_
  have b₁₅ : s₁₅.gpr .edi = B := (u₁₅.other _ (by decide)).trans b₁₄
  refine wp_stm b₁₅ (hin _ (by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, wr₁₂]) 20 (by omega)) fun s₁₆ u₁₆ => ?_
  have b₁₆ : s₁₆.gpr .edi = B := by rw [u₁₆.gpr]; exact b₁₅
  have rd₁₆ : s₁₆.rd = s.rd := by rw [u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, rd₁₂]
  have wr₁₆ : s₁₆.wr = s.wr := by rw [u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, wr₁₂]
  refine wp_ldm b₁₆ (hrd _ rd₁₆ wr₁₆ 284 (by omega)) fun s₁₇ u₁₇ => ?_
  refine wp_addi fun s₁₈ u₁₈ => wp_bswap fun s₁₉ u₁₉ => ?_
  have b₁₉ : s₁₉.gpr .edi = B := by
    rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide)]; exact b₁₆
  have rd₁₉ : s₁₉.rd = s.rd := by rw [u₁₉.rd, u₁₈.rd, u₁₇.rd, rd₁₆]
  have wr₁₉ : s₁₉.wr = s.wr := by rw [u₁₉.wr, u₁₈.wr, u₁₇.wr, wr₁₆]
  refine wp_stm b₁₉ (hin _ wr₁₉ 28 (by omega)) fun s₂₀ u₂₀ => ?_
  have b₂₀ : s₂₀.gpr .edi = B := by rw [u₂₀.gpr]; exact b₁₉
  refine wp_ldm b₂₀ (hrd _ (by rw [u₂₀.rd, rd₁₉]) (by rw [u₂₀.wr, wr₁₉]) 284 (by omega))
    fun s₂₁ u₂₁ => wp_addi fun s₂₂ u₂₂ => ?_
  have b₂₂ : s₂₂.gpr .edi = B := by rw [u₂₂.other _ (by decide), u₂₁.other _ (by decide)]; exact b₂₀
  refine wp_stm b₂₂ (hin _ (by rw [u₂₂.wr, u₂₁.wr, u₂₀.wr, wr₁₉]) 284 (by omega)) fun s₂₃ u₂₃ =>
    WP.block_nil ?_
  -- The memory, store by store.
  let c : BitVec 32 := s.mem.readW (VG.X86.addr B 284) 32
  let M₂ := s.mem.writeW (VG.X86.addr B 0) (s.mem.readW (VG.X86.addr B 272) 32)
  let M₄ := M₂.writeW (VG.X86.addr B 8) (s.mem.readW (VG.X86.addr B 276) 32)
  let M₆ := M₄.writeW (VG.X86.addr B 16) (s.mem.readW (VG.X86.addr B 280) 32)
  let M₁₀ := M₆.writeW (VG.X86.addr B 24) (bswap (c + 0))
  let M₁₂ := M₁₀.writeW (VG.X86.addr B 4) (s.mem.readW (VG.X86.addr B 272) 32)
  let M₁₄ := M₁₂.writeW (VG.X86.addr B 12) (s.mem.readW (VG.X86.addr B 276) 32)
  let M₁₆ := M₁₄.writeW (VG.X86.addr B 20) (s.mem.readW (VG.X86.addr B 280) 32)
  let M₂₀ := M₁₆.writeW (VG.X86.addr B 28) (bswap (c + 1))
  let M₂₃ := M₂₀.writeW (VG.X86.addr B 284) (c + 2)
  have m₂ : s₂.mem = M₂ := by rw [u₂.mem, u₁.gpr, u₁.mem]
  have m₄ : s₄.mem = M₄ := by
    rw [u₄.mem, u₃.gpr, u₃.mem, m₂]
    simp (disch := decide) only [M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit]
  have m₆ : s₆.mem = M₆ := by
    rw [u₆.mem, u₅.gpr, u₅.mem, m₄]
    simp (disch := decide) only [M₆, M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit]
  have m₁₀ : s₁₀.mem = M₁₀ := by
    rw [u₁₀.mem, u₉.gpr, u₈.gpr, u₇.gpr, u₉.mem, u₈.mem, u₇.mem, m₆]
    simp (disch := decide) only [M₁₀, M₆, M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit]; rfl
  have m₁₂ : s₁₂.mem = M₁₂ := by
    rw [u₁₂.mem, u₁₁.gpr, u₁₁.mem, m₁₀]
    simp (disch := decide) only [M₁₂, M₁₀, M₆, M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit]
  have m₁₄ : s₁₄.mem = M₁₄ := by
    rw [u₁₄.mem, u₁₃.gpr, u₁₃.mem, m₁₂]
    simp (disch := decide) only [M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit]
  have m₁₆ : s₁₆.mem = M₁₆ := by
    rw [u₁₆.mem, u₁₅.gpr, u₁₅.mem, m₁₄]
    simp (disch := decide) only [M₁₆, M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit]
  have m₂₀ : s₂₀.mem = M₂₀ := by
    rw [u₂₀.mem, u₁₉.gpr, u₁₈.gpr, u₁₇.gpr, u₁₉.mem, u₁₈.mem, u₁₇.mem, m₁₆]
    simp (disch := decide) only [M₂₀, M₁₆, M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit]; rfl
  have m₂₃ : s₂₃.mem = M₂₃ := by
    rw [u₂₃.mem, u₂₂.gpr, u₂₁.gpr, u₂₂.mem, u₂₁.mem, m₂₀]
    simp (disch := decide) only [M₂₃, M₂₀, M₁₆, M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit]; rfl
  have b₂₃ : s₂₃.gpr .edi = B := by rw [u₂₃.gpr]; exact b₂₂
  refine h s₂₃ (fun k hk => ?_) ?_ ?_ (fun r hr => ?_) ?_ ?_
  · have e : VG.Proof.Aes.X86.Q s₂₃ k = M₂₃.readW (VG.X86.addr B (4 * k)) 32 := by
      simp only [VG.Proof.Aes.X86.Q, wordAddr]; rw [show s₂₃.gpr sb = B from b₂₃, m₂₃]
    rw [e]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [M₂₃, M₂₀, M₁₆, M₁₄, M₁₂, M₁₀, M₆, M₄, M₂, VG.Proof.Aes.X86.rd_wr_ne hfit,
      Mem.readW_writeW_self32, VG.Proof.Aes.X86.ctrSlot, VG.Proof.Aes.X86.cw, VG.Proof.Aes.X86.cnum, cwOff, cNum, c] <;> rfl
  · simp only [VG.Proof.Aes.X86.cnum, cNum, m₂₃, M₂₃, Mem.readW_writeW_self32, c]
  · rw [m₂₃]
    have c32 : ∀ o, o + 4 ≤ 32 → (VG.Proof.Aes.X86.reg32 B 32).Contains (VG.X86.addr B o) (32 / 8) :=
      fun o ho => VG.Proof.Aes.X86.reg_contains (by omega) ho (by decide)
    have m1 : VG.Proof.Aes.X86.reg32 B 32 ∈ [VG.Proof.Aes.X86.reg32 B 32, ⟨VG.X86.addr B cNum, 4⟩] := by simp
    have m2 : (⟨VG.X86.addr B cNum, 4⟩ : Region) ∈ [VG.Proof.Aes.X86.reg32 B 32, ⟨VG.X86.addr B cNum, 4⟩] := by simp
    exact (((((((((Frame.refl _ _).writeW m1 _ (c32 0 (by omega))).writeW m1 _ (c32 8 (by omega))).writeW
      m1 _ (c32 16 (by omega))).writeW m1 _ (c32 24 (by omega))).writeW m1 _ (c32 4 (by omega))).writeW
      m1 _ (c32 12 (by omega))).writeW m1 _ (c32 20 (by omega))).writeW m1 _ (c32 28 (by omega))).writeW
      m2 _ (Region.contains_self _ _)
  · simp only [u₂₃.gpr, u₂₂.other r hr, u₂₁.other r hr, u₂₀.gpr, u₁₉.other r hr, u₁₈.other r hr,
      u₁₇.other r hr, u₁₆.gpr, u₁₅.other r hr, u₁₄.gpr, u₁₃.other r hr, u₁₂.gpr, u₁₁.other r hr,
      u₁₀.gpr, u₉.other r hr, u₈.other r hr, u₇.other r hr, u₆.gpr, u₅.other r hr, u₄.gpr,
      u₃.other r hr, u₂.gpr, u₁.other r hr]
  · rw [u₂₃.rd, u₂₂.rd, u₂₁.rd, u₂₀.rd, rd₁₉]
  · rw [u₂₃.wr, u₂₂.wr, u₂₁.wr, u₂₀.wr, wr₁₉]

/-! ## The counter blocks as states -/

/-- The counter blocks `2g` and `2g + 1` in the slots, as `InRel` has them. -/
theorem ctr_inRel {Q' : Nat → BitVec 32} {m : Mem} {B : BitVec 32} {icb : Spec.Gcm.Block} {g : Nat}
    (hq : ∀ k < 8, Q' k = VG.Proof.Aes.X86.ctrSlot m B k)
    (hcw : ∀ w < 3, ∀ i < 4, ∀ j < 8, (VG.Proof.Aes.X86.cw m B w).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - (4 * w + i)) + j))
    (hnum : VG.Proof.Aes.X86.cnum m B = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g)) :
    InRel Q' (fun b => ctrState icb (2 * g + b)) := by
  intro b hb i hi16 j hj
  simp only [ctrState, getD_eq _ hi16, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi16, hq _ (by omega)]
  unfold VG.Proof.Aes.X86.ctrSlot
  by_cases h12 : i < 12
  · rw [ite_eq_left (by omega), ite_eq_left h12, toBytes_getD _ hi16, BitVec.getLsbD_extractLsb',
      show (b + 2 * (i / 4)) / 2 = i / 4 by omega, hcw (i / 4) (by omega) (i % 4) (by omega) j hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega
  · rw [ite_eq_right (by omega), ite_eq_right h12, show b + 2 * (i / 4) - 6 = b by omega,
      show 8 * (i % 4) + j = 8 * (i % 4) + j from rfl, VG.Proof.Aes.X86.bswap_bit _ (by omega) hj, hnum,
      BitVec.getLsbD_extractLsb', BitVec.add_assoc, ← BitVec.ofNat_add]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

/-! ## XOR into the data -/

/-- XOR `v` into the 4 bytes at `a`. -/
def xorW (m : Mem) (a : Addr) (v : BitVec 32) : Mem := m.writeW a (m.readW a 32 ^^^ v)

theorem xorW_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    VG.Proof.Aes.X86.xorW m a v x = if (x - a).toNat < 4 then m x ^^^ v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold VG.Proof.Aes.X86.xorW Mem.writeW Mem.write
  split
  · rename_i h
    have hx : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have := Mem.extractLsb'_read m a (n := 4) h
    rw [hx] at this
    rw [← this]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

/-- The data after `d` bytes: the keystream `ks` XORed into the first `d`
of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n d : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < d then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := by
  split <;> bv_omega

/-- One word of keystream XORed in. -/
theorem dataInv_word {m₀ m : Mem} {D : Addr} {n d : Nat} {ks : Nat → Byte} {v : BitVec 32}
    (hn : 16 * n < 2 ^ 64) (hd : d + 4 ≤ 16 * n) (h : VG.Proof.Aes.X86.DataInv m₀ m D n d ks)
    (hks : ∀ t < 4, v.extractLsb' (8 * t) 8 = ks (d + t)) :
    VG.Proof.Aes.X86.DataInv m₀ (VG.Proof.Aes.X86.xorW m (D + BitVec.ofNat 64 d) v) D n (d + 4) ks ∧
      Frame [⟨D, 16 * n⟩] m (VG.Proof.Aes.X86.xorW m (D + BitVec.ofNat 64 d) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [VG.Proof.Aes.X86.xorW_apply, VG.Proof.Aes.X86.off_toNat D (by omega) (by omega), h i hi]
    by_cases h1 : d ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - d < 4
      · rw [ite_eq_left h2, hks _ h2, ite_eq_right (show ¬ i < d by omega),
          ite_eq_left (show i < d + 4 by omega), show d + (i - d) = i by omega]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < d by omega),
          ite_eq_right (show ¬ i < d + 4 by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - d < 4 by omega),
        ite_eq_left (show i < d by omega), ite_eq_left (show i < d + 4 by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [VG.Proof.Aes.X86.xorW_apply, ite_eq_right]
    have : (BitVec.ofNat 64 d).toNat = d := by simp; omega
    bv_omega

theorem dataInv_frame {m₀ m m' : Mem} {D : Addr} {n d : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : VG.Proof.Aes.X86.DataInv m₀ m D n d ks) : VG.Proof.Aes.X86.DataInv m₀ m' D n d ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

theorem dataInv_mono {m₀ m : Mem} {D : Addr} {n d d' : Nat} {ks : Nat → Byte}
    (h : VG.Proof.Aes.X86.DataInv m₀ m D n d ks) (hd : 16 * n ≤ d) (hd' : 16 * n ≤ d') : VG.Proof.Aes.X86.DataInv m₀ m D n d' ks := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < d by omega), ite_eq_left (show i < d' by omega)]

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ks_of_inRel {Q' : Nat → BitVec 32} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : InRel Q' (fun b => Spec.Aes.cipher R w (ctrState icb (2 * g + b)))) {b k t : Nat} (hb : b < 2)
    (hk : k < 4) (ht : t < 4) :
    (Q' (2 * k + b)).extractLsb' (8 * t) 8 = VG.Proof.Aes.X86.keyStream R w icb (16 * (2 * g + b) + 4 * k + t) := by
  apply byte_ext
  intro j hj
  have := h b hb (4 * k + t) (by omega) j hj
  rw [show b + 2 * ((4 * k + t) / 4) = 2 * k + b by omega, show (4 * k + t) % 4 = t by omega] at this
  rw [BitVec.getLsbD_extractLsb', this, VG.Proof.Aes.X86.keyStream,
    show (16 * (2 * g + b) + 4 * k + t) / 16 = 2 * g + b by omega,
    show (16 * (2 * g + b) + 4 * k + t) % 16 = 4 * k + t by omega]
  simp [hj]

/-- XOR word `k` of keystream block `b` into the data at `esi`. -/
def xw (b k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (16 * b + 4 * k))), xorS .eax (2 * k + b), .store (at_ .esi (16 * b + 4 * k)) .eax]

theorem xorBlock_eq (b : Nat) : xorBlock b = VG.Proof.Aes.X86.xw b 0 ++ (VG.Proof.Aes.X86.xw b 1 ++ (VG.Proof.Aes.X86.xw b 2 ++ VG.Proof.Aes.X86.xw b 3)) := by
  simp [xorBlock, VG.Proof.Aes.X86.xw, List.range, List.range.loop]

/-- The buffers the XOR phase uses. -/
structure XBufs (Dp B : BitVec 32) (n : Nat) (s : State) : Prop where
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  dat : VG.Proof.Aes.X86.reg32 Dp (16 * n) ∈ s.wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  scr : VG.Proof.Aes.X86.reg32 B 2048 ∈ s.wr
  sep : (VG.Proof.Aes.X86.reg32 Dp (16 * n)).Disjoint (VG.Proof.Aes.X86.reg32 B 2048)

theorem XBufs.congr {Dp B : BitVec 32} {n : Nat} {s s' : State} (h : VG.Proof.Aes.X86.XBufs Dp B n s) (hwr : s'.wr = s.wr) :
    VG.Proof.Aes.X86.XBufs Dp B n s' := ⟨h.fitD, hwr ▸ h.dat, h.fitB, hwr ▸ h.scr, h.sep⟩

theorem xorWord_wp {s : State} {Dp B : BitVec 32} {n g b k : Nat} {m₀ : Mem} {ks : Nat → Byte}
    {rest : List Instr} {P : State → Prop} (hbuf : VG.Proof.Aes.X86.XBufs Dp B n s) (hb : b < 2) (hk : k < 4)
    (hn : 2 * g + b < n) (hesi : s.gpr .esi = Dp + BitVec.ofNat 32 (32 * g)) (hedi : s.gpr .edi = B)
    (hinv : VG.Proof.Aes.X86.DataInv m₀ s.mem (Dp.setWidth 64) n (16 * (2 * g + b) + 4 * k) ks)
    (hks : ∀ t < 4, (VG.Proof.Aes.X86.Q s (2 * k + b)).extractLsb' (8 * t) 8 = ks (16 * (2 * g + b) + 4 * k + t))
    (h : ∀ s', VG.Proof.Aes.X86.DataInv m₀ s'.mem (Dp.setWidth 64) n (16 * (2 * g + b) + 4 * k + 4) ks →
      Frame [VG.Proof.Aes.X86.reg32 Dp (16 * n)] s.mem s'.mem → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' P) :
    WP isa (.block (VG.Proof.Aes.X86.xw b k ++ rest)) s P := by
  have hfit := hbuf.fitD
  have ea : VG.X86.addr (Dp + BitVec.ofNat 32 (32 * g)) (16 * b + 4 * k) =
      Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g + b) + 4 * k) := by
    rw [VG.Proof.Aes.X86.addr_add, show 32 * g + (16 * b + 4 * k) = 16 * (2 * g + b) + 4 * k by omega]
    exact addr_eq (by omega)
  have hin : InRegions s.wr (VG.X86.addr (Dp + BitVec.ofNat 32 (32 * g)) (16 * b + 4 * k)) 4 := by
    rw [VG.Proof.Aes.X86.addr_add]; exact VG.Proof.Aes.X86.in_reg hbuf.dat hfit (by omega) (by decide)
  simp only [VG.Proof.Aes.X86.xw, List.cons_append, List.nil_append]
  refine wp_ldm hesi (VG.Proof.Aes.X86.in_rd hin) fun s₁ u₁ => ?_
  refine wp_xorm (B := B) (o := 4 * (2 * k + b)) (by rw [u₁.other _ (by decide)]; exact hedi)
    (by rw [u₁.rd, u₁.wr]; exact VG.Proof.Aes.X86.in_rd (VG.Proof.Aes.X86.in_reg hbuf.scr hbuf.fitB (by omega) (by decide))) fun s₂ u₂ => ?_
  refine wp_stm (B := Dp + BitVec.ofNat 32 (32 * g))
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hesi)
    (by rw [u₂.wr, u₁.wr]; exact hin) fun s₃ u₃ => ?_
  have hm : s₃.mem = VG.Proof.Aes.X86.xorW s.mem (Dp.setWidth 64 + BitVec.ofNat 64 (16 * (2 * g + b) + 4 * k))
      (VG.Proof.Aes.X86.Q s (2 * k + b)) := by
    have e : VG.Proof.Aes.X86.Q s (2 * k + b) = s.mem.readW (VG.X86.addr B (4 * (2 * k + b))) 32 := by
      simp only [VG.Proof.Aes.X86.Q, wordAddr]; rw [show s.gpr sb = B from hedi]
    rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, ea, VG.Proof.Aes.X86.xorW, e]
  have hst := VG.Proof.Aes.X86.dataInv_word (v := VG.Proof.Aes.X86.Q s (2 * k + b)) (by omega) (by omega) hinv hks
  rw [← hm] at hst
  refine h s₃ hst.1 hst.2 (fun r hr => ?_) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
  rw [u₃.gpr, u₂.other r hr, u₁.other r hr]

/-! ## The XOR phase of a group -/

/-- Before the XOR phase of group `g`: the keystream is in the slots. -/
structure XPre (m₀ : Mem) (Dp B : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ : State) : Prop where
  buf : VG.Proof.Aes.X86.XBufs Dp B n s₃
  hg : 2 * g < n
  edi : s₃.gpr .edi = B
  dslot : s₃.mem.readW (VG.X86.addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * g)
  nslot : s₃.mem.readW (VG.X86.addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * g)
  data : VG.Proof.Aes.X86.DataInv m₀ s₃.mem (Dp.setWidth 64) n (32 * g) ks
  ks : ∀ b < 2, ∀ k < 4, ∀ t < 4,
    (VG.Proof.Aes.X86.Q s₃ (2 * k + b)).extractLsb' (8 * t) 8 = ks (16 * (2 * g + b) + 4 * k + t)

/-- After `k` words of the group have been XORed in, from `s₃`. -/
structure XS (m₀ : Mem) (Dp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : VG.Proof.Aes.X86.DataInv m₀ s.mem (Dp.setWidth 64) n (32 * g + 4 * k) ks
  frame : Frame [VG.Proof.Aes.X86.reg32 Dp (16 * n)] s₃.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr

section Xor

variable {m₀ : Mem} {Dp B : BitVec 32} {n g : Nat} {ks : Nat → Byte} {s₃ : State}

theorem XPre.qsame (hp : VG.Proof.Aes.X86.XPre m₀ Dp B n g ks s₃) {k : Nat} {s : State} (hs : VG.Proof.Aes.X86.XS m₀ Dp n g ks s₃ k s) (j : Nat)
    (hj : j < 8) : VG.Proof.Aes.X86.Q s j = VG.Proof.Aes.X86.Q s₃ j := by
  simp only [VG.Proof.Aes.X86.Q, wordAddr, hs.keep sb (by decide), show s₃.gpr sb = B from hp.edi]
  refine hs.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact (hp.buf.sep.sub_right (VG.Proof.Aes.X86.part_sub_reg hp.buf.fitB (by omega))).symm

theorem xs_step (hp : VG.Proof.Aes.X86.XPre m₀ Dp B n g ks s₃) (hesi₃ : s₃.gpr .esi = Dp + BitVec.ofNat 32 (32 * g))
    {b k : Nat} (hb : b < 2) (hk : k < 4) (hn : 2 * g + b < n) {s : State} (hs : VG.Proof.Aes.X86.XS m₀ Dp n g ks s₃ (4 * b + k) s) {rest : List Instr}
    {P : State → Prop} (h : ∀ s', VG.Proof.Aes.X86.XS m₀ Dp n g ks s₃ (4 * b + k + 1) s' → WP isa (.block rest) s' P) :
    WP isa (.block (VG.Proof.Aes.X86.xw b k ++ rest)) s P := by
  have hesi : s.gpr .esi = s₃.gpr .esi := hs.keep _ (by decide)
  refine VG.Proof.Aes.X86.xorWord_wp (m₀ := m₀) (ks := ks) (hp.buf.congr hs.wr) hb hk hn (Dp := Dp) (g := g) ?_ ?_ ?_ ?_
    fun s' d f o rd wr => h s' ⟨?_, hs.frame.trans f, fun r hr => (o r hr).trans (hs.keep r hr),
      rd.trans hs.rd, wr.trans hs.wr⟩
  · rw [hesi, hesi₃]
  · rw [hs.keep _ (by decide)]; exact hp.edi
  · have := hs.data; rwa [show 32 * g + 4 * (4 * b + k) = 16 * (2 * g + b) + 4 * k by omega] at this
  · intro t ht; rw [hp.qsame hs _ (by omega)]; exact hp.ks b hb k hk t ht
  · rwa [show 32 * g + 4 * (4 * b + k + 1) = 16 * (2 * g + b) + 4 * k + 4 by omega]

theorem xorTwo_eq : xorTwo = VG.Proof.Aes.X86.xw 0 0 ++ (VG.Proof.Aes.X86.xw 0 1 ++ (VG.Proof.Aes.X86.xw 0 2 ++ (VG.Proof.Aes.X86.xw 0 3 ++ (VG.Proof.Aes.X86.xw 1 0 ++ (VG.Proof.Aes.X86.xw 1 1 ++
    (VG.Proof.Aes.X86.xw 1 2 ++ (VG.Proof.Aes.X86.xw 1 3 ++ ([addI .esi 32, subI .ebp 2] : List Instr)))))))) := by
  simp only [xorTwo, VG.Proof.Aes.X86.xorBlock_eq, List.append_assoc]

theorem xorOne_eq : xorOne = VG.Proof.Aes.X86.xw 0 0 ++ (VG.Proof.Aes.X86.xw 0 1 ++ (VG.Proof.Aes.X86.xw 0 2 ++ (VG.Proof.Aes.X86.xw 0 3 ++
    ([subR .ebp .ebp] : List Instr)))) := by
  simp only [xorOne, VG.Proof.Aes.X86.xorBlock_eq, List.append_assoc]

/-- Between the two parts of the XOR phase. -/
structure XMid (m₀ : Mem) (Dp B : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop where
  frame : Frame [VG.Proof.Aes.X86.reg32 Dp (16 * n)] s₃.mem s.mem
  keep : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  post : (s.gpr .ebp = 0 ∧ VG.Proof.Aes.X86.DataInv m₀ s.mem (Dp.setWidth 64) n (16 * n) ks) ∨
    (s.gpr .ebp = BitVec.ofNat 32 (n - 2 * (g + 1)) ∧ 0 < n - 2 * (g + 1) ∧
      s.gpr .esi = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      VG.Proof.Aes.X86.DataInv m₀ s.mem (Dp.setWidth 64) n (32 * (g + 1)) ks)

/-- After the XOR phase: ZF is set if no data is left. -/
structure XDone (m₀ : Mem) (Dp B : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop where
  frame : Frame [VG.Proof.Aes.X86.reg32 Dp (16 * n), ⟨VG.X86.addr B dOff, 8⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  post : (s.zf = some true ∧ VG.Proof.Aes.X86.DataInv m₀ s.mem (Dp.setWidth 64) n (16 * n) ks) ∨
    (s.zf = some false ∧ 2 * g + 2 < n ∧ VG.Proof.Aes.X86.DataInv m₀ s.mem (Dp.setWidth 64) n (32 * (g + 1)) ks ∧
      s.mem.readW (VG.X86.addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.mem.readW (VG.X86.addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * (g + 1)))

theorem XPre.congr (hp : VG.Proof.Aes.X86.XPre m₀ Dp B n g ks s₃) {s : State} (hm : s.mem = s₃.mem) (hwr : s.wr = s₃.wr)
    (he : s.gpr .edi = s₃.gpr .edi) : VG.Proof.Aes.X86.XPre m₀ Dp B n g ks s :=
  have hq : VG.Proof.Aes.X86.Q s = VG.Proof.Aes.X86.Q s₃ := VG.Proof.Aes.X86.Q_congr he hm
  ⟨hp.buf.congr hwr, hp.hg, he.trans hp.edi, hm ▸ hp.dslot, hm ▸ hp.nslot, hm ▸ hp.data,
    fun b hb k hk t ht => by rw [hq]; exact hp.ks b hb k hk t ht⟩

theorem xorGroup_wp (hp : VG.Proof.Aes.X86.XPre m₀ Dp B n g ks s₃) : WP isa xorGroup s₃ (VG.Proof.Aes.X86.XDone m₀ Dp B n g ks s₃) := by
  have hg := hp.hg
  have hfitD := hp.buf.fitD
  have hin : ∀ (t : State), t.wr = s₃.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (VG.X86.addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact VG.Proof.Aes.X86.in_reg hp.buf.scr hp.buf.fitB ho (by decide)
  unfold xorGroup
  refine WP.seq ?_
  refine wp_ldm (B := B) (o := dOff) hp.edi (VG.Proof.Aes.X86.in_rd (hin _ rfl _ (by decide))) fun s₄ u₄ => ?_
  refine wp_ldm (B := B) (o := nOff) (by rw [u₄.other _ (by decide)]; exact hp.edi)
    (by rw [u₄.rd, u₄.wr]; exact VG.Proof.Aes.X86.in_rd (hin _ rfl _ (by decide))) fun s₅ u₅ => ?_
  refine wp_cmpi fun s₆ u₆ hcf _ => WP.block_nil ?_
  have hm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  have hwr₆ : s₆.wr = s₃.wr := by rw [u₆.wr, u₅.wr, u₄.wr]
  have hrd₆ : s₆.rd = s₃.rd := by rw [u₆.rd, u₅.rd, u₄.rd]
  have g₆ : ∀ r, r ≠ .esi → r ≠ .ebp → s₆.gpr r = s₃.gpr r := fun r h1 h2 => by
    rw [u₆.gpr, u₅.other r h2, u₄.other r h1]
  have hesi₆ : s₆.gpr .esi = Dp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, hp.dslot]
  have hebp₆ : s₆.gpr .ebp = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.gpr, u₅.gpr, u₄.mem, hp.nslot]
  have hp₆ : VG.Proof.Aes.X86.XPre m₀ Dp B n g ks s₆ := hp.congr hm₆ hwr₆ (g₆ _ (by decide) (by decide))
  have x₀ : VG.Proof.Aes.X86.XS m₀ Dp n g ks s₆ 0 s₆ := ⟨by simpa using hp₆.data, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  rw [u₅.gpr, u₄.mem, hp.nslot, toNat_ofNat_lt (by omega)] at hcf
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.X86.XMid m₀ Dp B n g ks s₆) ?_ fun s hs => ?_)
  · refine WP.ite (!decide (n - 2 * g < (2 : BitVec 32).toNat)) (by simp [X86.eval, hcf])
      (fun hb => ?_) (fun hb => ?_)
    · -- Two blocks.
      have h2 : 2 ≤ n - 2 * g := by simpa using hb
      rw [VG.Proof.Aes.X86.xorTwo_eq]
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 0) (k := 0) (by omega) (by omega) (by omega) x₀ fun s₇ x₇ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 0) (k := 1) (by omega) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 0) (k := 2) (by omega) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 0) (k := 3) (by omega) (by omega) (by omega) x₉ fun s₁₀ x₁₀ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 1) (k := 0) (by omega) (by omega) (by omega) x₁₀ fun s₁₁ x₁₁ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 1) (k := 1) (by omega) (by omega) (by omega) x₁₁ fun s₁₂ x₁₂ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 1) (k := 2) (by omega) (by omega) (by omega) x₁₂ fun s₁₃ x₁₃ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 1) (k := 3) (by omega) (by omega) (by omega) x₁₃ fun s₁₄ x₁₄ => ?_
      refine wp_addi fun s₁₅ u₁₅ => wp_subi fun s₁₆ u₁₆ _ _ => WP.block_nil ?_
      have hd : VG.Proof.Aes.X86.DataInv m₀ s₁₆.mem (Dp.setWidth 64) n (32 * (g + 1)) ks := by
        rw [u₁₆.mem, u₁₅.mem]; have := x₁₄.data; rwa [show 32 * g + 4 * (4 * 1 + 3 + 1) = 32 * (g + 1) by omega] at this
      refine ⟨by rw [u₁₆.mem, u₁₅.mem]; exact x₁₄.frame, fun r h1 h2 h3 => ?_,
        by rw [u₁₆.rd, u₁₅.rd, x₁₄.rd], by rw [u₁₆.wr, u₁₅.wr, x₁₄.wr], ?_⟩
      · rw [u₁₆.other r h3, u₁₅.other r h2, x₁₄.keep r h1]
      · have eb : s₁₆.gpr .ebp = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
          rw [u₁₆.gpr, u₁₅.other _ (by decide), x₁₄.keep _ (by decide), hebp₆]
          have : n ≤ 2 ^ 28 := by omega
          bv_omega
        by_cases hl : n - 2 * g = 2
        · refine .inl ⟨by rw [eb, show n - 2 * (g + 1) = 0 by omega]; rfl, VG.Proof.Aes.X86.dataInv_mono hd (by omega) (by omega)⟩
        · refine .inr ⟨eb, by omega, ?_, hd⟩
          rw [u₁₆.other _ (by decide), u₁₅.gpr, x₁₄.keep _ (by decide), hesi₆, BitVec.add_assoc,
            show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
          congr 2
    · -- The last block.
      have h1 : n - 2 * g = 1 := by simp at hb; omega
      rw [VG.Proof.Aes.X86.xorOne_eq]
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 0) (k := 0) (by omega) (by omega) (by omega) x₀ fun s₇ x₇ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 0) (k := 1) (by omega) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 0) (k := 2) (by omega) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
      refine VG.Proof.Aes.X86.xs_step hp₆ hesi₆ (b := 0) (k := 3) (by omega) (by omega) (by omega) x₉ fun s₁₀ x₁₀ => ?_
      refine wp_sub fun s₁₁ u₁₁ _ => WP.block_nil ?_
      refine ⟨by rw [u₁₁.mem]; exact x₁₀.frame, fun r h1 _ h3 => by rw [u₁₁.other r h3, x₁₀.keep r h1],
        by rw [u₁₁.rd, x₁₀.rd], by rw [u₁₁.wr, x₁₀.wr], .inl ⟨by rw [u₁₁.gpr]; exact BitVec.sub_self _, ?_⟩⟩
      rw [u₁₁.mem]
      have := x₁₀.data
      rwa [show 32 * g + 4 * (4 * 0 + 3 + 1) = 16 * n by omega] at this
  · -- Store the pointer and the count.
    have hedi : s.gpr .edi = B := by rw [hs.keep _ (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide), hp.edi]
    refine wp_stm hedi (hin _ (by rw [hs.wr, hwr₆]) dOff (by decide)) fun s₇ u₇ => ?_
    refine wp_stm (by rw [u₇.gpr]; exact hedi) (hin _ (by rw [u₇.wr, hs.wr, hwr₆]) nOff (by decide))
      fun s₈ u₈ => wp_test fun s₉ u₉ hz => WP.block_nil ?_
    have hfitB := hp.buf.fitB
    have fr : Frame [⟨VG.X86.addr B dOff, 8⟩] s.mem s₉.mem := by
      rw [u₉.mem, u₈.mem, u₇.mem]
      have hm : (⟨VG.X86.addr B dOff, 8⟩ : Region) ∈ [⟨VG.X86.addr B dOff, 8⟩] := List.mem_singleton_self _
      exact ((Frame.refl _ _).writeW hm _ (VG.Proof.Aes.X86.part_contains hfitB (by decide) (by decide) (by decide) (by decide))).writeW
        hm _ (VG.Proof.Aes.X86.part_contains hfitB (by decide) (by decide) (by decide) (by decide))
    have dsj : ∀ r ∈ [(⟨VG.X86.addr B dOff, 8⟩ : Region)], Region.Disjoint (VG.Proof.Aes.X86.reg32 Dp (16 * n)) r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hp.buf.sep.sub_right (VG.Proof.Aes.X86.part_sub_reg hfitB (by decide))
    have hds : s₉.mem.readW (VG.X86.addr B dOff) 32 = s.gpr .esi := by
      rw [u₉.mem, u₈.mem, u₇.mem, u₇.gpr, VG.Proof.Aes.X86.rd_wr_ne hfitB _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide), Mem.readW_writeW_self32]
    have hns : s₉.mem.readW (VG.X86.addr B nOff) 32 = s.gpr .ebp := by
      rw [u₉.mem, u₈.mem, u₇.gpr, u₇.mem, Mem.readW_writeW_self32]
    refine ⟨?_, fun r h1 h2 h3 => ?_, by rw [u₉.rd, u₈.rd, u₇.rd, hs.rd, hrd₆],
      by rw [u₉.wr, u₈.wr, u₇.wr, hs.wr, hwr₆], ?_⟩
    · rw [← hm₆]
      exact (hs.frame.mono (by simp)).trans (fr.mono (by simp))
    · rw [u₉.gpr, u₈.gpr, u₇.gpr, hs.keep r h1 h2 h3, g₆ r h2 h3]
    · rw [hz, u₈.gpr, u₇.gpr]
      rcases hs.post with ⟨e, d⟩ | ⟨e, hpos, ei, d⟩
      · exact .inl ⟨by rw [e]; rfl, VG.Proof.Aes.X86.dataInv_frame fr dsj (by omega) d⟩
      · refine .inr ⟨?_, by omega, VG.Proof.Aes.X86.dataInv_frame fr dsj (by omega) d, by rw [hds, ei], by rw [hns, e]⟩
        rw [e, BitVec.and_self, ofNat_beq_zero (by omega)]
        simp only [Option.some.injEq, decide_eq_false_iff_not]; omega

end Xor


end VG.Proof.Aes.X86

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `B` the scratch buffer, `Dp` the data (`n` blocks), `icb`
the first counter block. -/
structure GSetup (s₂ : State) (B Dp : BitVec 32) (n R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) :
    Prop where
  scr : VG.Proof.Aes.X86.reg32 B 2048 ∈ s₂.wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  dat : VG.Proof.Aes.X86.reg32 Dp (16 * n) ∈ s₂.wr
  fitD : Dp.toNat + 16 * n ≤ 2 ^ 32
  sep : (VG.Proof.Aes.X86.reg32 Dp (16 * n)).Disjoint (VG.Proof.Aes.X86.reg32 B 2048)
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  argIn : InRegions (s₂.rd ++ s₂.wr) (VG.X86.addr (s₂.gpr .esp) 8) 4
  argR : s₂.mem.readW (VG.X86.addr (s₂.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  argSep : Region.Disjoint ⟨VG.X86.addr (s₂.gpr .esp) 8, 4⟩ (VG.Proof.Aes.X86.reg32 B 2048)
  argSepD : Region.Disjoint ⟨VG.X86.addr (s₂.gpr .esp) 8, 4⟩ (VG.Proof.Aes.X86.reg32 Dp (16 * n))
  keys : VG.Proof.Aes.X86.KeysAt s₂.mem B R w
  cw : ∀ v < 3, ∀ i < 4, ∀ j < 8,
    (VG.Proof.Aes.X86.cw s₂.mem B v).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - (4 * v + i)) + j)

/-- The memory the groups write: the layers' slots, the counter, the data
pointer and the count, and the data. -/
abbrev gRegions (B Dp : BitVec 32) (n : Nat) : List Region :=
  [VG.Proof.Aes.X86.reg32 B 256, ⟨VG.X86.addr B cNum, 12⟩, VG.Proof.Aes.X86.reg32 Dp (16 * n)]

/-- Before group `g`. -/
structure GInv (m₀ : Mem) (s₂ : State) (B Dp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 2 * g < n
  base : s.gpr sb = B
  esp : s.gpr .esp = s₂.gpr .esp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (VG.Proof.Aes.X86.gRegions B Dp n) s₂.mem s.mem
  num : VG.Proof.Aes.X86.cnum s.mem B = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g)
  dslot : s.mem.readW (VG.X86.addr B dOff) 32 = Dp + BitVec.ofNat 32 (32 * g)
  nslot : s.mem.readW (VG.X86.addr B nOff) 32 = BitVec.ofNat 32 (n - 2 * g)
  data : VG.Proof.Aes.X86.DataInv m₀ s.mem (Dp.setWidth 64) n (32 * g) (VG.Proof.Aes.X86.keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (B Dp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr sb = B
  esp : s.gpr .esp = s₂.gpr .esp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (VG.Proof.Aes.X86.gRegions B Dp n) s₂.mem s.mem
  data : VG.Proof.Aes.X86.DataInv m₀ s.mem (Dp.setWidth 64) n (16 * n) (VG.Proof.Aes.X86.keyStream R w icb)

section
variable {s₂ : State} {B Dp : BitVec 32} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
  (hs : VG.Proof.Aes.X86.GSetup s₂ B Dp n R w icb)
include hs

/-- A part of the scratch buffer at offset `o` is apart from the regions the
groups write if it is beyond the slots and the counter. -/
theorem GSetup.gdisj {o l : Nat} (h1 : 256 ≤ o) (h2 : o + l ≤ cNum ∨ cNum + 12 ≤ o) (h3 : o + l ≤ 2048) :
    ∀ r ∈ VG.Proof.Aes.X86.gRegions B Dp n, Region.Disjoint ⟨VG.X86.addr B o, l⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
    rw [← VG.Proof.Aes.X86.addr_zero]; exact VG.Proof.Aes.X86.part_disj hs.fitB h3 (by omega) (.inr h1)
  · exact VG.Proof.Aes.X86.part_disj hs.fitB h3 (by simp only [cNum]; omega) h2
  · exact (hs.sep.sub_right (VG.Proof.Aes.X86.part_sub_reg hs.fitB h3)).symm

theorem GSetup.argDisj : ∀ r ∈ VG.Proof.Aes.X86.gRegions B Dp n, Region.Disjoint ⟨VG.X86.addr (s₂.gpr .esp) 8, 4⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.argSep.sub_right (Region.sub_prefix (by omega))
  · exact hs.argSep.sub_right (VG.Proof.Aes.X86.part_sub_reg hs.fitB (by simp only [cNum]; omega))
  · exact hs.argSepD

theorem GSetup.dataDisj {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r (VG.Proof.Aes.X86.reg32 B 2048)) :
    ∀ r ∈ rs, Region.Disjoint (VG.Proof.Aes.X86.reg32 Dp (16 * n)) r := fun r hr => hs.sep.sub_right (h r hr)

/-- One group: from before group `g`, to after the last group (ZF set) or
before group `g + 1`. -/
theorem group_ok {m₀ : Mem} {g : Nat} {s : State} (hi : VG.Proof.Aes.X86.GInv m₀ s₂ B Dp n R w icb g s) :
    WP isa group s fun s' => (s'.zf = some true ∧ VG.Proof.Aes.X86.GDone m₀ s₂ B Dp n R w icb s') ∨
      (s'.zf = some false ∧ VG.Proof.Aes.X86.GInv m₀ s₂ B Dp n R w icb (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hfitB := hs.fitB
  have hfitD := hs.fitD
  have hscr : VG.Proof.Aes.X86.reg32 B 2048 ∈ s.wr := hi.wr ▸ hs.scr
  unfold group
  refine WP.seq (VG.Proof.Aes.X86.ctrBlocks_wp hi.base hfitB hscr fun s₁ hq₁ hn₁ f₁ o₁ rd₁ wr₁ => ?_)
  have hb₁ : s₁.gpr sb = B := (o₁ sb (by decide)).trans hi.base
  have f₁sub : ∀ r ∈ [VG.Proof.Aes.X86.reg32 B 32, (⟨VG.X86.addr B cNum, 4⟩ : Region)], ∃ r' ∈ VG.Proof.Aes.X86.gRegions B Dp n, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Aes.X86.reg32 B 256, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨VG.X86.addr B cNum, 12⟩, by simp, Region.sub_prefix (by omega)⟩
  have hf₁ : Frame (VG.Proof.Aes.X86.gRegions B Dp n) s₂.mem s₁.mem := hi.frame.trans (f₁.sub f₁sub)
  have hesp₁ : s₁.gpr .esp = s₂.gpr .esp := (o₁ _ (by decide)).trans hi.esp
  have hp : VG.Proof.Aes.X86.EncPre s₁ R w :=
    { scr := by rw [hb₁, wr₁, hi.wr]; exact hs.scr
      fit := by rw [hb₁]; exact hfitB
      rounds := hs.rounds
      argIn := by rw [rd₁, wr₁, hi.rd, hi.wr, hesp₁]; exact hs.argIn
      argR := by
        rw [hesp₁, ← hs.argR]
        exact hf₁.readW (Region.contains_self _ _) hs.argDisj (by decide)
      argSep := by rw [hesp₁, hb₁]; exact hs.argSep.sub_right (Region.sub_prefix (by omega))
      keys := by
        rw [hb₁]
        intro j hj
        refine keyRel_congr (hs.keys j hj) fun k hk => ?_
        have := VG.Proof.Aes.X86.keyOff_le (j := j) hR
        exact hf₁.readW (Region.contains_self _ _)
          (hs.gdisj (by simp only [lastKey] at this; omega) (.inr (by simp only [cNum]; omega))
            (by simp only [lastKey] at this; omega)) (by decide) }
  have hcw : ∀ v < 3, ∀ i < 4, ∀ j < 8,
      (VG.Proof.Aes.X86.cw s.mem B v).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - (4 * v + i)) + j) := by
    intro v hv i hi' j hj
    have e : VG.Proof.Aes.X86.cw s.mem B v = VG.Proof.Aes.X86.cw s₂.mem B v :=
      hi.frame.readW (Region.contains_self _ _)
        (hs.gdisj (by simp only [cwOff]; omega) (.inl (by simp only [cwOff, cNum]; omega))
          (by simp only [cwOff]; omega)) (by decide)
    rw [e]; exact hs.cw v hv i hi' j hj
  have hin : InRel (VG.Proof.Aes.X86.Q s₁) (fun b => ctrState icb (2 * g + b)) := VG.Proof.Aes.X86.ctr_inRel hq₁ hcw hi.num
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.encrypt2_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₁] at fr₃
  have hb₃ : s₃.gpr .edi = B := hc₃.base.trans hb₁
  have d256 : ∀ r ∈ [VG.Proof.Aes.X86.reg32 B 256], Region.Disjoint (VG.Proof.Aes.X86.reg32 Dp (16 * n)) r :=
    hs.dataDisj fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
  have d32 : ∀ r ∈ [VG.Proof.Aes.X86.reg32 B 32, (⟨VG.X86.addr B cNum, 4⟩ : Region)], Region.Disjoint (VG.Proof.Aes.X86.reg32 Dp (16 * n)) r :=
    hs.dataDisj fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by omega)
      · exact VG.Proof.Aes.X86.part_sub_reg hfitB (by decide)
  have slot13 : ∀ o, 288 ≤ o → o + 4 ≤ 296 → s₃.mem.readW (VG.X86.addr B o) 32 = s.mem.readW (VG.X86.addr B o) 32 := by
    intro o h1 h2
    rw [fr₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
        rw [← VG.Proof.Aes.X86.addr_zero]; exact VG.Proof.Aes.X86.part_disj hfitB (by omega) (by omega) (.inr (by omega))) (by decide)]
    exact f₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show Region.Disjoint _ ⟨B.setWidth 64, 32⟩
        rw [← VG.Proof.Aes.X86.addr_zero]; exact VG.Proof.Aes.X86.part_disj hfitB (by omega) (by omega) (.inr (by omega))
      · exact VG.Proof.Aes.X86.part_disj hfitB (by omega) (by decide) (.inr (by simp only [cNum]; omega))) (by decide)
  have hx : VG.Proof.Aes.X86.XPre m₀ Dp B n g (VG.Proof.Aes.X86.keyStream R w icb) s₃ :=
    { buf := ⟨hfitD, by rw [hc₃.wr, wr₁, hi.wr]; exact hs.dat, hfitB, by rw [hc₃.wr, wr₁, hi.wr]; exact hs.scr,
        hs.sep⟩
      hg := hi.hg
      edi := hb₃
      dslot := by rw [slot13 _ (by decide) (by decide)]; exact hi.dslot
      nslot := by rw [slot13 _ (by decide) (by decide)]; exact hi.nslot
      data := VG.Proof.Aes.X86.dataInv_frame fr₃ d256 (by omega) (VG.Proof.Aes.X86.dataInv_frame f₁ d32 (by omega) hi.data)
      ks := fun b hb k hk t ht => by
        rw [VG.Proof.Aes.X86.ks_of_inRel hin₃ hb hk ht] }
  refine WP.mono (VG.Proof.Aes.X86.xorGroup_wp hx) fun s' hd => ?_
  have keep : ∀ r, r ∉ tmpRegs → r ≠ .esi → s'.gpr r = s.gpr r := fun r h1 h2 =>
    (hd.keep r (fun h => h1 (h ▸ by decide)) h2 (fun h => h1 (h ▸ by decide))).trans
      ((hc₃.keep r h1 h2).trans (o₁ r (fun h => h1 (h ▸ by decide))))
  have base' : s'.gpr sb = B := (keep sb (by decide) (by decide)).trans hi.base
  have esp' : s'.gpr .esp = s₂.gpr .esp := (keep .esp (by decide) (by decide)).trans hi.esp
  have rd' : s'.rd = s₂.rd := by rw [hd.rd, hc₃.rd, rd₁, hi.rd]
  have wr' : s'.wr = s₂.wr := by rw [hd.wr, hc₃.wr, wr₁, hi.wr]
  have frame' : Frame (VG.Proof.Aes.X86.gRegions B Dp n) s₂.mem s'.mem := by
    refine hf₁.trans (Frame.trans (fr₃.sub fun r hr => ⟨VG.Proof.Aes.X86.reg32 B 256, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩) (hd.frame.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Aes.X86.reg32 Dp (16 * n), by simp, fun _ h => h⟩
    · exact ⟨⟨VG.X86.addr B cNum, 12⟩, by simp, VG.Proof.Aes.X86.part_sub hfitB (by simp only [cNum]; omega)
        (by simp only [dOff, cNum]; omega) (by simp only [dOff, cNum]; omega)⟩
  rcases hd.post with ⟨z, d⟩ | ⟨z, h4, d, ds, ns⟩
  · exact .inl ⟨z, base', esp', rd', wr', frame', d⟩
  · refine .inr ⟨z, ⟨by omega, base', esp', rd', wr', frame', ?_, ds, ns, d⟩⟩
    have e₁ : VG.Proof.Aes.X86.cnum s'.mem B = VG.Proof.Aes.X86.cnum s₃.mem B :=
      hd.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (hs.sep.sub_right (VG.Proof.Aes.X86.part_sub_reg hfitB (by decide))).symm
        · exact VG.Proof.Aes.X86.part_disj hfitB (by decide) (by decide) (.inl (by decide))) (by decide)
    have e₂ : VG.Proof.Aes.X86.cnum s₃.mem B = VG.Proof.Aes.X86.cnum s₁.mem B :=
      fr₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
        rw [← VG.Proof.Aes.X86.addr_zero]; exact VG.Proof.Aes.X86.part_disj hfitB (by decide) (by omega) (.inr (by decide))) (by decide)
    rw [e₁, e₂, hn₁, hi.num, BitVec.add_assoc]
    congr 1
    have : n ≤ 2 ^ 28 := by omega
    bv_omega

/-- The loop over the groups. -/
theorem groups_ok {m₀ : Mem} {s : State} (hi : VG.Proof.Aes.X86.GInv m₀ s₂ B Dp n R w icb 0 s) :
    WP isa (.loop group .ne) s (VG.Proof.Aes.X86.GDone m₀ s₂ B Dp n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ VG.Proof.Aes.X86.GInv m₀ s₂ B Dp n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (VG.Proof.Aes.X86.group_ok hs hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86.eval, z], d⟩
  · exact .inr ⟨by simp [X86.eval, z], n - 2 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Ctr32CT`. -/
section

/-!
# AES counter mode on x86 (32-bit): the contract, and constant time

The contract the proof is written against, and the constant-time half of
the proof: the taint analysis (`VG.X86.Taint`) starts with `esp` public
and knows where the arguments are and which of them are the base addresses
of the counter block, the data and the scratch buffer. The data pointer
and the count round-trip through public slots of the scratch buffer; the
stores of the keystream through the data pointer forget them, and the code
stores them again from the registers.
-/

namespace VG.Proof.Aes

open Spec.Gcm

open _root_.VG.X86 in
/-- X86 (32-bit) contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds:
usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut
[u64; 256])`, whose arguments are on the stack: XORs the AES counter-mode
keystream from the counter block at `counter` into the `n` blocks at `data`, and
advances the counter block by `n`.

The code may read `schedule` (240 bytes) and the arguments (24 bytes above
the return address), and read and write `counter` (16 bytes), `data`
(`16 n` bytes) and `scratch` (2048 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, `schedule`,
the arguments or the return address; nothing may wrap around the end of the
(32-bit) address space. `rounds` is 10, 12 or 14. `esp` and the arguments
are public; the key schedule, the counter block and the data are secret. -/
def ctr32X86 : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(VG.X86.arg s 0).setWidth 64, 240⟩
    let counter : Region := ⟨(VG.X86.arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(VG.X86.arg s 3).setWidth 64, 16 * (VG.X86.arg s 4).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 5).setWidth 64, 2048⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint counter ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint counter ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (VG.X86.arg s 3).toNat + 16 * (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 5).toNat + 2048 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    ((VG.X86.arg s 1).toNat = 10 ∨ (VG.X86.arg s 1).toNat = 12 ∨ (VG.X86.arg s 1).toNat = 14)
  post s s' :=
    let ciph := VG.Spec.Gcm.aesWith (VG.X86.arg s 1).toNat
      (Spec.Aes.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (16 * ((VG.X86.arg s 1).toNat + 1)))
    VG.Spec.Gcm.blocksAt s'.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat =
        ctr32 ciph (VG.Spec.Gcm.blockAt s.mem ((VG.X86.arg s 2).setWidth 64))
          (VG.Spec.Gcm.blocksAt s.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat) ∧
      VG.Spec.Gcm.blockAt s'.mem ((VG.X86.arg s 2).setWidth 64) =
        Nat.repeat inc32 (VG.X86.arg s 4).toNat (VG.Spec.Gcm.blockAt s.mem ((VG.X86.arg s 2).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, VG.X86.arg s₁ i = VG.X86.arg s₂ i

end VG.Proof.Aes

namespace VG.Proof.Aes.X86

open VG VG.X86

/-! ## The precondition -/

section
variable (s : State)

abbrev schP : BitVec 32 := VG.X86.arg s 0
abbrev nRounds : Nat := (VG.X86.arg s 1).toNat
abbrev ctrP : BitVec 32 := VG.X86.arg s 2
abbrev datP : BitVec 32 := VG.X86.arg s 3
abbrev nBlk : Nat := (VG.X86.arg s 4).toNat
abbrev scrP : BitVec 32 := VG.X86.arg s 5
abbrev schR : Region := VG.Proof.Aes.X86.reg32 (VG.Proof.Aes.X86.schP s) 240
abbrev ctrR : Region := VG.Proof.Aes.X86.reg32 (VG.Proof.Aes.X86.ctrP s) 16
abbrev datR : Region := VG.Proof.Aes.X86.reg32 (VG.Proof.Aes.X86.datP s) (16 * VG.Proof.Aes.X86.nBlk s)
abbrev scrR : Region := VG.Proof.Aes.X86.reg32 (VG.Proof.Aes.X86.scrP s) 2048
abbrev argR : Region := ⟨argAddr s 0, 24⟩
abbrev retR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `ctr32X86.pre`, by name. -/
structure CPre (s : State) : Prop where
  rd : s.rd = [VG.Proof.Aes.X86.schR s, VG.Proof.Aes.X86.argR s]
  wr : s.wr = [VG.Proof.Aes.X86.ctrR s, VG.Proof.Aes.X86.datR s, VG.Proof.Aes.X86.scrR s]
  dSC : (VG.Proof.Aes.X86.schR s).Disjoint (VG.Proof.Aes.X86.ctrR s)
  dSD : (VG.Proof.Aes.X86.schR s).Disjoint (VG.Proof.Aes.X86.datR s)
  dSB : (VG.Proof.Aes.X86.schR s).Disjoint (VG.Proof.Aes.X86.scrR s)
  dCD : (VG.Proof.Aes.X86.ctrR s).Disjoint (VG.Proof.Aes.X86.datR s)
  dCB : (VG.Proof.Aes.X86.ctrR s).Disjoint (VG.Proof.Aes.X86.scrR s)
  dDB : (VG.Proof.Aes.X86.datR s).Disjoint (VG.Proof.Aes.X86.scrR s)
  aC : (VG.Proof.Aes.X86.argR s).Disjoint (VG.Proof.Aes.X86.ctrR s)
  aD : (VG.Proof.Aes.X86.argR s).Disjoint (VG.Proof.Aes.X86.datR s)
  aB : (VG.Proof.Aes.X86.argR s).Disjoint (VG.Proof.Aes.X86.scrR s)
  rC : (VG.Proof.Aes.X86.retR s).Disjoint (VG.Proof.Aes.X86.ctrR s)
  rD : (VG.Proof.Aes.X86.retR s).Disjoint (VG.Proof.Aes.X86.datR s)
  rB : (VG.Proof.Aes.X86.retR s).Disjoint (VG.Proof.Aes.X86.scrR s)
  fS : (VG.Proof.Aes.X86.schP s).toNat + 240 ≤ 2 ^ 32
  fC : (VG.Proof.Aes.X86.ctrP s).toNat + 16 ≤ 2 ^ 32
  fD : (VG.Proof.Aes.X86.datP s).toNat + 16 * VG.Proof.Aes.X86.nBlk s ≤ 2 ^ 32
  fB : (VG.Proof.Aes.X86.scrP s).toNat + 2048 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rounds : VG.Proof.Aes.X86.nRounds s = 10 ∨ VG.Proof.Aes.X86.nRounds s = 12 ∨ VG.Proof.Aes.X86.nRounds s = 14

theorem CPre.of {s : State} (h : Proof.Aes.ctr32X86.pre s) : VG.Proof.Aes.X86.CPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

/-! ## Constant time -/

/-- The taint analysis starts with `esp` public, and the words holding
`counter`, `data` and `scratch` known to be the base addresses of the
writable regions. -/
def ctrτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [16, 0, 2048], argLen := 28,
    argBases := [(12, 0), (16, 1), (24, 2)] }

theorem ctr_wf₀ {s : State} (hp : VG.Proof.Aes.X86.CPre s) : VG.X86.Taint.Wf VG.Proof.Aes.X86.ctrτ₀ s := by
  have hC := hp.fC; have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [VG.Proof.Aes.X86.ctrτ₀]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.dCD, hp.dCB⟩, hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [VG.Proof.Aes.X86.toNat_setWidth32] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rC hp.aC
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [VG.Proof.Aes.X86.ctrτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]

theorem ctr_agree₀ {s₁ s₂ : State} (h₁ : Proof.Aes.ctr32X86.pre s₁) (h₂ : Proof.Aes.ctr32X86.pre s₂)
    (hpub : Proof.Aes.ctr32X86.pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.Aes.X86.ctrτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := CPre.of h₁; have hp₂ := CPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Aes.X86.ctr_wf₀ hp₁, VG.Proof.Aes.X86.ctr_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Aes.X86.ctrτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [VG.Proof.Aes.X86.ctrR, VG.Proof.Aes.X86.datR, VG.Proof.Aes.X86.scrR, VG.Proof.Aes.X86.ctrP, VG.Proof.Aes.X86.datP, VG.Proof.Aes.X86.nBlk, VG.Proof.Aes.X86.scrP, ha 2 (by omega), ha 3 (by omega),
      ha 4 (by omega), ha 5 (by omega)]
  · simp only [VG.Proof.Aes.X86.ctrτ₀] at hk
    rw [show VG.X86.Taint.depth ctrτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 28) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 28) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32X86.pre Proof.Aes.ctr32X86.pub Impl.Aes.X86.ctr32 :=
  VG.Taint.constantTime (A := VG.X86.taint) VG.Proof.Aes.X86.ctrτ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Aes.X86.ctr_agree₀ h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Ctr32`. -/
section

/-!
# AES counter mode on x86 (32-bit): the whole function

The prologue saves the callee-saved registers in the scratch buffer, copies
the counter block's words to it and writes back the final counter; the key
loop (`Keys.lean`) and the group loop (`Group.lean`) do the rest, and the
epilogue restores the registers. Constant time is `Ctr32CT.lean`.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_bswap wp_ldm wp_xorm wp_stm sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

theorem arg_eq (s : State) (i : Nat) : VG.X86.arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

/-! ## The prologue -/

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  edi : s.gpr .edi = VG.Proof.Aes.X86.scrP s₀
  esi : s.gpr .esi = VG.X86.arg s₀ 1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (VG.Proof.Aes.X86.scrP s₀) 256, 32⟩, ⟨addr (VG.Proof.Aes.X86.ctrP s₀) 12, 4⟩] s₀.mem s.mem
  saved : ∀ p ∈ savedRegs, s.mem.readW (addr (VG.Proof.Aes.X86.scrP s₀) p.2) 32 = s₀.gpr p.1
  cw : ∀ v < 3, VG.Proof.Aes.X86.cw s.mem (VG.Proof.Aes.X86.scrP s₀) v = s₀.mem.readW (addr (VG.Proof.Aes.X86.ctrP s₀) (4 * v)) 32
  cnum : VG.Proof.Aes.X86.cnum s.mem (VG.Proof.Aes.X86.scrP s₀) = bswap (s₀.mem.readW (addr (VG.Proof.Aes.X86.ctrP s₀) 12) 32)
  ctr : s.mem.readW (addr (VG.Proof.Aes.X86.ctrP s₀) 12) 32 =
    bswap (bswap (s₀.mem.readW (addr (VG.Proof.Aes.X86.ctrP s₀) 12) 32) + VG.X86.arg s₀ 4)

theorem prologue_eq : saveRegs 5 ++ ctrSetup ++ keySetup = ([
    .mov .eax (.mem (at_ .esp 24)), .store (at_ .eax 256) .ebx, .store (at_ .eax 260) .esi,
    .store (at_ .eax 264) .edi, .store (at_ .eax 268) .ebp, .mov .edi (.reg .eax),
    .mov .ecx (.mem (at_ .esp 12)),
    .mov .eax (.mem (at_ .ecx 0)), .store (at_ .edi 272) .eax,
    .mov .eax (.mem (at_ .ecx 4)), .store (at_ .edi 276) .eax,
    .mov .eax (.mem (at_ .ecx 8)), .store (at_ .edi 280) .eax,
    .mov .eax (.mem (at_ .ecx 12)), .bswap .eax, .store (at_ .edi 284) .eax,
    .alu .add .eax (.mem (at_ .esp 20)), .bswap .eax, .store (at_ .ecx 12) .eax,
    .mov .esi (.mem (at_ .esp 8))] : List Instr) := rfl

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Aes.X86.CPre s₀) :
    WP isa (.block (saveRegs 5 ++ ctrSetup ++ keySetup)) s₀ (VG.Proof.Aes.X86.P1 s₀) := by
  have fB := hp.fB; have fC := hp.fC; have fSp := hp.fSp
  let B := VG.Proof.Aes.X86.scrP s₀
  let C := VG.Proof.Aes.X86.ctrP s₀
  let E := s₀.gpr .esp
  have hwB : VG.Proof.Aes.X86.reg32 B 2048 ∈ s₀.wr := by
    rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hwC : VG.Proof.Aes.X86.reg32 C 16 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self ..
  have hrA : VG.Proof.Aes.X86.argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  -- The arguments are readable, and apart from the counter and the scratch buffer.
  have argC : ∀ i < 6, (VG.Proof.Aes.X86.argR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 24⟩ : Region).Contains _ _
    exact VG.Proof.Aes.X86.part_contains (N := 28) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 6, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨VG.Proof.Aes.X86.argR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have bIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact VG.Proof.Aes.X86.in_reg hwB fB ho (by decide)
  have cIn : ∀ (t : State), t.wr = s₀.wr → ∀ o, o + 4 ≤ 16 → InRegions t.wr (addr C o) 4 :=
    fun t ht o ho => by rw [ht]; exact VG.Proof.Aes.X86.in_reg hwC fC ho (by decide)
  have bC : ∀ o, o + 4 ≤ 2048 → (VG.Proof.Aes.X86.scrR s₀).Contains (addr B o) 4 := fun o ho => VG.Proof.Aes.X86.reg_contains fB ho (by decide)
  have cC : ∀ o, o + 4 ≤ 16 → (VG.Proof.Aes.X86.ctrR s₀).Contains (addr C o) 4 := fun o ho => VG.Proof.Aes.X86.reg_contains fC ho (by decide)
  rw [VG.Proof.Aes.X86.prologue_eq]
  refine wp_ldm (B := E) (o := 24) rfl (argIn _ rfl 5 (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = B := by rw [u₁.gpr]; rfl
  refine wp_stm e₁ (bIn _ u₁.wr 256 (by omega)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (bIn _ (by rw [u₂.wr, u₁.wr]) 260 (by omega)) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.gpr, u₂.gpr]; exact e₁) (bIn _ (by rw [u₃.wr, u₂.wr, u₁.wr]) 264 (by omega))
    fun s₄ u₄ => ?_
  refine wp_stm (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁)
    (bIn _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 268 (by omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .edi → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₆.other r h2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r h1]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have edi₆ : s₆.gpr .edi = B := by rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]; exact e₁
  -- The saves.
  let M₄ := (((s₀.mem.writeW (addr B 256) (s₀.gpr .ebx)).writeW (addr B 260) (s₀.gpr .esi)).writeW
    (addr B 264) (s₀.gpr .edi)).writeW (addr B 268) (s₀.gpr .ebp)
  have m₆ : s₆.mem = M₄ := by
    simp only [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr]
    rw [u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide),
      u₁.other .ebp (by decide), u₁.mem]
  have f₆ : Frame [VG.Proof.Aes.X86.reg32 B 2048] s₀.mem s₆.mem := by
    rw [m₆]
    have hm := List.mem_singleton_self (VG.Proof.Aes.X86.reg32 B 2048)
    exact ((((Frame.refl _ _).writeW hm _ (bC 256 (by omega))).writeW hm _ (bC 260 (by omega))).writeW hm _
      (bC 264 (by omega))).writeW hm _ (bC 268 (by omega))
  -- The counter pointer.
  refine wp_ldm (B := E) (o := 12) (by rw [g₆ _ (by decide) (by decide)])
    (argIn _ rd₆ 2 (by omega)) fun s₇ u₇ => ?_
  have e₇ : s₇.gpr .ecx = C := by
    rw [u₇.gpr, f₆.readW (argC 2 (by omega)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.aB) (by decide)]; rfl
  have dCB : ∀ r ∈ [VG.Proof.Aes.X86.reg32 B 2048], (VG.Proof.Aes.X86.ctrR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.dCB
  have dAB : ∀ r ∈ [VG.Proof.Aes.X86.reg32 B 2048], (VG.Proof.Aes.X86.argR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.aB
  have hm := List.mem_singleton_self (VG.Proof.Aes.X86.reg32 B 2048)
  -- The counter block's words.
  let c : Nat → BitVec 32 := fun o => s₀.mem.readW (addr C o) 32
  refine wp_ldm (B := C) (o := 0) e₇ (VG.Proof.Aes.X86.in_rd (cIn _ (by rw [u₇.wr, wr₆]) 0 (by omega))) fun s₈ u₈ => ?_
  have v₈ : s₈.gpr .eax = c 0 := by
    rw [u₈.gpr, u₇.mem]; exact f₆.readW (cC 0 (by omega)) dCB (by decide)
  have edi₈ : s₈.gpr .edi = B := by rw [u₈.other _ (by decide), u₇.other _ (by decide)]; exact edi₆
  refine wp_stm edi₈ (bIn _ (by rw [u₈.wr, u₇.wr, wr₆]) 272 (by omega)) fun s₉ u₉ => ?_
  have f₉ : Frame [VG.Proof.Aes.X86.reg32 B 2048] s₀.mem s₉.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem]; exact f₆.writeW hm _ (bC 272 (by omega))
  have ecx₉ : s₉.gpr .ecx = C := by rw [u₉.gpr, u₈.other _ (by decide)]; exact e₇
  refine wp_ldm (B := C) (o := 4) ecx₉ (VG.Proof.Aes.X86.in_rd (cIn _ (by rw [u₉.wr, u₈.wr, u₇.wr, wr₆]) 4 (by omega)))
    fun s₁₀ u₁₀ => ?_
  have v₁₀ : s₁₀.gpr .eax = c 4 := by rw [u₁₀.gpr]; exact f₉.readW (cC 4 (by omega)) dCB (by decide)
  have edi₁₀ : s₁₀.gpr .edi = B := by rw [u₁₀.other _ (by decide), u₉.gpr]; exact edi₈
  refine wp_stm edi₁₀ (bIn _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]) 276 (by omega)) fun s₁₁ u₁₁ => ?_
  have f₁₁ : Frame [VG.Proof.Aes.X86.reg32 B 2048] s₀.mem s₁₁.mem := by
    rw [u₁₁.mem, u₁₀.mem]; exact f₉.writeW hm _ (bC 276 (by omega))
  have ecx₁₁ : s₁₁.gpr .ecx = C := by rw [u₁₁.gpr, u₁₀.other _ (by decide)]; exact ecx₉
  have wr₁₁ : s₁₁.wr = s₀.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]
  have rd₁₁ : s₁₁.rd = s₀.rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆]
  refine wp_ldm (B := C) (o := 8) ecx₁₁ (VG.Proof.Aes.X86.in_rd (cIn _ wr₁₁ 8 (by omega))) fun s₁₂ u₁₂ => ?_
  have v₁₂ : s₁₂.gpr .eax = c 8 := by rw [u₁₂.gpr]; exact f₁₁.readW (cC 8 (by omega)) dCB (by decide)
  have edi₁₂ : s₁₂.gpr .edi = B := by
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr]; exact edi₈
  refine wp_stm edi₁₂ (bIn _ (by rw [u₁₂.wr, wr₁₁]) 280 (by omega)) fun s₁₃ u₁₃ => ?_
  have f₁₃ : Frame [VG.Proof.Aes.X86.reg32 B 2048] s₀.mem s₁₃.mem := by
    rw [u₁₃.mem, u₁₂.mem]; exact f₁₁.writeW hm _ (bC 280 (by omega))
  have ecx₁₃ : s₁₃.gpr .ecx = C := by rw [u₁₃.gpr, u₁₂.other _ (by decide)]; exact ecx₁₁
  refine wp_ldm (B := C) (o := 12) ecx₁₃ (VG.Proof.Aes.X86.in_rd (cIn _ (by rw [u₁₃.wr, u₁₂.wr, wr₁₁]) 12 (by omega)))
    fun s₁₄ u₁₄ => wp_bswap fun s₁₅ u₁₅ => ?_
  have v₁₅ : s₁₅.gpr .eax = bswap (c 12) := by
    rw [u₁₅.gpr, u₁₄.gpr]; congr 1; exact f₁₃.readW (cC 12 (by omega)) dCB (by decide)
  have edi₁₅ : s₁₅.gpr .edi = B := by
    rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr]; exact edi₁₂
  have wr₁₅ : s₁₅.wr = s₀.wr := by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]
  have rd₁₅ : s₁₅.rd = s₀.rd := by rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, rd₁₁]
  refine wp_stm edi₁₅ (bIn _ wr₁₅ 284 (by omega)) fun s₁₆ u₁₆ => ?_
  have f₁₆ : Frame [VG.Proof.Aes.X86.reg32 B 2048] s₀.mem s₁₆.mem := by
    rw [u₁₆.mem, u₁₅.mem, u₁₄.mem]; exact f₁₃.writeW hm _ (bC 284 (by omega))
  have esp₁₆ : s₁₆.gpr .esp = E := by
    rw [u₁₆.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide),
      u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      g₆ _ (by decide) (by decide)]
  refine wp_addm (B := E) (o := 20) esp₁₆
    (argIn _ (by rw [u₁₆.rd, rd₁₅]) 4 (by omega)) fun s₁₇ u₁₇ => wp_bswap fun s₁₈ u₁₈ => ?_
  have v₁₈ : s₁₈.gpr .eax = bswap (bswap (c 12) + VG.X86.arg s₀ 4) := by
    rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, v₁₅, VG.Proof.Aes.X86.arg_eq]
    congr 2
    exact f₁₆.readW (argC 4 (by omega)) dAB (by decide)
  have ecx₁₈ : s₁₈.gpr .ecx = C := by
    rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, u₁₅.other _ (by decide),
      u₁₄.other _ (by decide)]; exact ecx₁₃
  refine wp_stm ecx₁₈ (cIn _ (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, wr₁₅]) 12 (by omega)) fun s₁₉ u₁₉ => ?_
  have esp₁₉ : s₁₉.gpr .esp = E := by
    rw [u₁₉.gpr, u₁₈.other .esp (by decide), u₁₇.other .esp (by decide)]; exact esp₁₆
  refine wp_ldm (B := E) (o := 8) esp₁₉ (argIn _ (by rw [u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, rd₁₅]) 1 (by omega))
    fun s₂₀ u₂₀ => WP.block_nil ?_
  -- The memory at the end.
  let M₁₆ := ((((M₄.writeW (addr B 272) (c 0)).writeW (addr B 276) (c 4)).writeW (addr B 280) (c 8)).writeW
    (addr B 284) (bswap (c 12)))
  let M := M₁₆.writeW (addr C 12) (bswap (bswap (c 12) + VG.X86.arg s₀ 4))
  have m₂₀ : s₂₀.mem = M := by
    rw [u₂₀.mem, u₁₉.mem, v₁₈, u₁₈.mem, u₁₇.mem, u₁₆.mem, v₁₅, u₁₅.mem, u₁₄.mem, u₁₃.mem, v₁₂,
      u₁₂.mem, u₁₁.mem, v₁₀, u₁₀.mem, u₉.mem, v₈, u₈.mem, u₇.mem, m₆]
  have sC : (⟨addr B 256, 32⟩ : Region).Contains (addr B 256) (32 / 8) :=
    VG.Proof.Aes.X86.part_contains fB (by omega) (by omega) (by omega) (by decide)
  have hmB : (⟨addr B 256, 32⟩ : Region) ∈ [⟨addr B 256, 32⟩, ⟨addr C 12, 4⟩] := List.mem_cons_self ..
  have hmC : (⟨addr C 12, 4⟩ : Region) ∈ [⟨addr B 256, 32⟩, ⟨addr C 12, 4⟩] := by simp
  have cB : ∀ o, 256 ≤ o → o + 4 ≤ 288 → (⟨addr B 256, 32⟩ : Region).Contains (addr B o) (32 / 8) :=
    fun o h1 h2 => VG.Proof.Aes.X86.part_contains fB (by omega) h1 (by omega) (by decide)
  have fr : Frame [⟨addr B 256, 32⟩, ⟨addr C 12, 4⟩] s₀.mem s₂₀.mem := by
    rw [m₂₀]
    exact ((((((((Frame.refl _ _).writeW hmB _ (cB 256 (by omega) (by omega))).writeW hmB _
      (cB 260 (by omega) (by omega))).writeW hmB _ (cB 264 (by omega) (by omega))).writeW hmB _
      (cB 268 (by omega) (by omega))).writeW hmB _ (cB 272 (by omega) (by omega))).writeW hmB _
      (cB 276 (by omega) (by omega))).writeW hmB _ (cB 280 (by omega) (by omega))).writeW hmB _
      (cB 284 (by omega) (by omega)) |>.writeW hmC _ (Region.contains_self _ _)
  -- Reads of the scratch buffer through the write of the counter.
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  have rdB : ∀ o, o + 4 ≤ 2048 → M.readW (addr B o) 32 = M₁₆.readW (addr B o) 32 := fun o ho =>
    VG.Proof.Aes.X86.rd_wr_other hp.dCB.symm (bC o ho) (cC 12 (by omega))
  have g₂₀ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → r ≠ .esi → s₂₀.gpr r = s₀.gpr r := by
    intro r h1 h2 h3 h4
    rw [u₂₀.other r h4, u₁₉.gpr, u₁₈.other r h1, u₁₇.other r h1, u₁₆.gpr, u₁₅.other r h1, u₁₄.other r h1,
      u₁₃.gpr, u₁₂.other r h1, u₁₁.gpr, u₁₀.other r h1, u₉.gpr, u₈.other r h1, u₇.other r h2,
      g₆ r h1 h3]
  refine ⟨g₂₀ _ (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, fr, fun p hp' => ?_,
    fun v hv => ?_, ?_, ?_⟩
  · rw [u₂₀.other _ (by decide), u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr]
    exact edi₁₅
  · rw [u₂₀.gpr, ← u₂₀.mem, VG.Proof.Aes.X86.arg_eq]
    exact fr.readW (w := 32) (argC 1 (by omega)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.aB.sub_right (VG.Proof.Aes.X86.part_sub_reg fB (by omega))
      · exact hp.aC.sub_right (VG.Proof.Aes.X86.part_sub_reg fC (by omega))) (by decide)
  · rw [u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, rd₁₅]
  · rw [u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, wr₁₅]
  · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> rw [m₂₀, rdB _ (by omega)] <;>
      simp (disch := decide) only [M₁₆, M₄, VG.Proof.Aes.X86.rd_wr_ne fB', Mem.readW_writeW_self32]
  · rw [m₂₀]
    simp only [VG.Proof.Aes.X86.cw, cwOff]
    rw [rdB _ (by omega)]
    rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;>
      simp (disch := decide) only [M₁₆, M₄, VG.Proof.Aes.X86.rd_wr_ne fB', Mem.readW_writeW_self32] <;> rfl
  · rw [m₂₀]; simp only [VG.Proof.Aes.X86.cnum, cNum]; rw [rdB _ (by omega)]
    simp only [M₁₆, Mem.readW_writeW_self32]; rfl
  · rw [m₂₀]; exact Mem.readW_writeW_self32 _ _ _

/-! ## The counter block and the data, as blocks -/

/-- The counter, as the scratch buffer holds it. -/
theorem icb_lo (m : Mem) {C : BitVec 32} (hC : C.toNat + 16 ≤ 2 ^ 32) :
    bswap (m.readW (addr C 12) 32) = (Spec.Gcm.blockAt m (C.setWidth 64)).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega
  rw [e, VG.Proof.Aes.X86.bswap_bit _ (by omega) (by omega), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega,
    blockAt_bit _ _ (by omega) (by omega), VG.Proof.Aes.X86.readW_bit _ _ (by omega) (by omega),
    VG.Proof.Aes.X86.addr_add64 (by omega), show 12 + (3 - t / 8) = 15 - t / 8 by omega, addr_eq (by omega)]

/-- The counter block's word `v < 3`, bit by bit. -/
theorem cw_bits (m : Mem) {C : BitVec 32} (hC : C.toNat + 16 ≤ 2 ^ 32) {v i j : Nat} (hv : v < 3)
    (hi : i < 4) (hj : j < 8) :
    (m.readW (addr C (4 * v)) 32).getLsbD (8 * i + j) =
      (Spec.Gcm.blockAt m (C.setWidth 64)).getLsbD (8 * (15 - (4 * v + i)) + j) := by
  rw [VG.Proof.Aes.X86.readW_bit _ _ hi hj, blockAt_bit _ _ (by omega) hj, VG.Proof.Aes.X86.addr_add64 (by omega), addr_eq (by omega)]

/-- The counter block after the prologue: its first twelve bytes, and the
last four big-endian `c + n`. -/
theorem ctr_after {m m' : Mem} {C : BitVec 32} (hC : C.toNat + 16 ≤ 2 ^ 32) {N : BitVec 32} {n : Nat}
    (hN : N = BitVec.ofNat 32 n)
    (h12 : ∀ k < 12, m' (addr C k) = m (addr C k))
    (hw : m'.readW (addr C 12) 32 = bswap (bswap (m.readW (addr C 12) 32) + N)) :
    Spec.Gcm.blockAt m' (C.setWidth 64) = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m (C.setWidth 64)) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, ctrBlock_byte _ _ hk, ← addr_eq (by omega)]
  split
  · rename_i h; rw [toBytes_blockAt _ _ hk, ← addr_eq (by omega), h12 k h]
  · rename_i h
    rw [← VG.Proof.Aes.X86.icb_lo m hC, ← hN]
    refine byte_ext fun j hj => ?_
    have := VG.Proof.Aes.X86.readW_bit m' (addr C 12) (i := k - 12) (t := j) (by omega) hj
    rw [VG.Proof.Aes.X86.addr_add64 (by omega), show 12 + (k - 12) = k by omega, hw, VG.Proof.Aes.X86.bswap_bit _ (by omega) hj] at this
    rw [← this, BitVec.getLsbD_extractLsb']
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

theorem ctr32_of_dataInv {m₀ m : Mem} {D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : VG.Proof.Aes.X86.DataInv m₀ m D n (16 * n) (VG.Proof.Aes.X86.keyStream R w icb)) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ D n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc,
    ← BitVec.ofNat_add, h _ (by omega), ite_eq_left (by omega)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [VG.Proof.Aes.toBytes_ofBytes (by simp) hk, VG.Proof.Aes.X86.keyStream, show (16 * i + k) / 16 = i by omega,
    show (16 * i + k) % 16 = k by omega, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## Between the loops, and the epilogue -/

theorem groupSetup_ok {s : State} {B E : BitVec 32} (hb : s.gpr .edi = B) (he : s.gpr .esp = E)
    (hfit : B.toNat + 2048 ≤ 2 ^ 32) (hw : VG.Proof.Aes.X86.reg32 B 2048 ∈ s.wr)
    (hin : ∀ i, i = 3 ∨ i = 4 → InRegions (s.rd ++ s.wr) (addr E (4 + 4 * i)) 4)
    (hsep : ∀ i, i = 3 ∨ i = 4 → Region.Disjoint ⟨addr E (4 + 4 * i), 4⟩ (VG.Proof.Aes.X86.reg32 B 2048))
    {P : State → Prop}
    (h : ∀ s', s'.gpr .edi = B → s'.gpr .esp = E → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem.readW (addr B dOff) 32 = s.mem.readW (addr E 16) 32 →
      s'.mem.readW (addr B nOff) 32 = s.mem.readW (addr E 20) 32 →
      s'.zf = some (s.mem.readW (addr E 20) 32 == 0) → Frame [⟨addr B dOff, 8⟩] s.mem s'.mem →
      s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block groupSetup) s P := by
  have hin' : ∀ (t : State), t.wr = s.wr → ∀ o, o + 4 ≤ 2048 → InRegions t.wr (addr B o) 4 :=
    fun t ht o ho => by rw [ht]; exact VG.Proof.Aes.X86.in_reg hw hfit ho (by decide)
  have hm : (⟨addr B dOff, 8⟩ : Region) ∈ [⟨addr B dOff, 8⟩] := List.mem_singleton_self _
  refine wp_ldm (B := E) (o := 16) he (hin 3 (.inl rfl)) fun s₁ u₁ => ?_
  refine wp_stm (B := B) (o := dOff) (by rw [u₁.other _ (by decide)]; exact hb) (hin' _ u₁.wr _ (by decide))
    fun s₂ u₂ => ?_
  have f₂ : Frame [⟨addr B dOff, 8⟩] s.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW hm _ (VG.Proof.Aes.X86.part_contains hfit (by decide) (by decide) (by decide) (by decide))
  refine wp_ldm (B := E) (o := 20) (by rw [u₂.gpr, u₁.other _ (by decide)]; exact he)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 4 (.inr rfl)) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (o := nOff) (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb)
    (hin' _ (by rw [u₃.wr, u₂.wr, u₁.wr]) _ (by decide)) fun s₄ u₄ => wp_test fun s₅ u₅ hz => WP.block_nil ?_
  have v₃ : s₃.gpr .eax = s.mem.readW (addr E 20) 32 := by
    rw [u₃.gpr]
    exact f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hsep 4 (.inr rfl)).sub_right (VG.Proof.Aes.X86.part_sub_reg hfit (by decide))) (by decide)
  have hfit' := hfit
  refine h s₅ ?_ ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact hb
  · rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; exact he
  · rw [u₅.gpr, u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem,
      VG.Proof.Aes.X86.rd_wr_ne hfit _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [u₅.mem, u₄.mem, Mem.readW_writeW_self32, v₃]
  · rw [hz, u₄.gpr, v₃, BitVec.and_self]
  · rw [u₅.mem, u₄.mem, u₃.mem]
    exact f₂.writeW hm _ (VG.Proof.Aes.X86.part_contains hfit (by decide) (by decide) (by decide) (by decide))

theorem restore_ok {s : State} {B : BitVec 32} {N : Nat} {g : Reg → BitVec 32} (hb : s.gpr .edi = B)
    (hfit : B.toNat + N ≤ 2 ^ 32) (hw : VG.Proof.Aes.X86.reg32 B N ∈ s.wr) (hs : Spill.Saved s.mem (addr B) g savedRegs)
    (hN : 272 ≤ N := by omega) :
    WP isa (.block restoreRegs) s
      (Spill.Restored s · g ([(.ebx, 256), (.esi, 260), (.ebp, 268)] ++ [(.edi, 264)])) := by
  rw [show restoreRegs =
    Spill.restoreCode .edi ([(.ebx, 256), (.esi, 260), (.ebp, 268)] ++ [(.edi, 264)]) ++ [] from rfl]
  exact Spill.restoreBase_ok _ (by decide)
    (fun p h => have : p.2 + 4 ≤ 272 := by revert p h; decide
      by rw [hb]; exact VG.Proof.Aes.X86.in_rd (VG.Proof.Aes.X86.in_reg hw hfit (by omega) (by decide)))
    (by rw [hb]; exact hs.sub (by decide)) fun s' r => WP.block_nil r

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Aes.X86.CPre s₀) :
    WP isa Impl.Aes.X86.ctr32 s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Aes.ctr32X86.post s₀ s' := by
  have fB := hp.fB; have fC := hp.fC; have fD := hp.fD; have fS := hp.fS; have fSp := hp.fSp
  have hR : VG.Proof.Aes.X86.nRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  let B := VG.Proof.Aes.X86.scrP s₀
  let C := VG.Proof.Aes.X86.ctrP s₀
  let D := VG.Proof.Aes.X86.datP s₀
  let S := VG.Proof.Aes.X86.schP s₀
  let E := s₀.gpr .esp
  let R := VG.Proof.Aes.X86.nRounds s₀
  let n := VG.Proof.Aes.X86.nBlk s₀
  let w := Spec.Aes.bytesAt s₀.mem (S.setWidth 64) (16 * (R + 1))
  let icb := Spec.Gcm.blockAt s₀.mem (C.setWidth 64)
  have fS' : S.toNat + 240 ≤ 2 ^ 32 := fS
  have fB' : B.toNat + 2048 ≤ 2 ^ 32 := fB
  have fC' : C.toNat + 16 ≤ 2 ^ 32 := fC
  have fD' : D.toNat + 16 * n ≤ 2 ^ 32 := fD
  have fE' : E.toNat + 28 ≤ 2 ^ 32 := fSp
  have hR' : R ≤ 14 := hR
  have hwB : VG.Proof.Aes.X86.reg32 B 2048 ∈ s₀.wr := by
    rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hwD : VG.Proof.Aes.X86.reg32 D (16 * n) ∈ s₀.wr := by
    rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hrS : VG.Proof.Aes.X86.reg32 S 240 ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_self ..
  have hrA : VG.Proof.Aes.X86.argR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argC : ∀ i < 6, (VG.Proof.Aes.X86.argR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 24⟩ : Region).Contains _ _
    exact VG.Proof.Aes.X86.part_contains (N := 28) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 6, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨VG.Proof.Aes.X86.argR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  -- The prologue.
  unfold Impl.Aes.X86.ctr32
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.prologue_ok hp) fun s₁ h₁ => ?_)
  have F₁ := h₁.frame
  have d₁ : ∀ {r : Region}, r.Disjoint (VG.Proof.Aes.X86.scrR s₀) → r.Disjoint (VG.Proof.Aes.X86.ctrR s₀) →
      ∀ r' ∈ [(⟨addr B 256, 32⟩ : Region), ⟨addr C 12, 4⟩], r.Disjoint r' := by
    intro r h1 h2 r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h1.sub_right (VG.Proof.Aes.X86.part_sub_reg fB (by omega))
    · exact h2.sub_right (VG.Proof.Aes.X86.part_sub_reg fC (by omega))
  have arg₁ : ∀ i < 6, s₁.mem.readW (addr E (4 + 4 * i)) 32 = VG.X86.arg s₀ i := fun i hi =>
    F₁.readW (argC i hi) (d₁ hp.aB hp.aC) (by decide)
  have sched₁ : ∀ i < 240, s₁.mem (addr S i) = s₀.mem (addr S i) := fun i hi =>
    VG.Proof.Aes.X86.frame_one F₁ (VG.Proof.Aes.X86.reg_contains fS (by omega) (by decide)) (d₁ hp.dSB hp.dSC)
  have hk : VG.Proof.Aes.X86.KSetup s₁ B S R w :=
    { scr := by rw [h₁.wr]; exact hwB
      fitB := fB
      sch := by rw [h₁.rd]; exact List.mem_append_left _ hrS
      fitS := fS
      sep := hp.dSB
      rounds := hp.rounds
      base := h₁.edi
      argIn := fun i hi => by rw [h₁.esp]; exact argIn _ h₁.rd i (by omega)
      arg0 := by rw [h₁.esp]; exact arg₁ 0 (by omega)
      arg1 := by rw [h₁.esp, arg₁ 1 (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := fun i hi => by rw [h₁.esp]; exact hp.aB.sub_left (VG.Proof.Aes.X86.part_sub (N := 28) (b := E) fSp (by omega)
        (by omega) (by omega))
      w := fun i hi => by
        rw [sched₁ i (by omega)]
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        rw [addr_eq (by have := fS'; omega)] }
  have hi₁ : VG.Proof.Aes.X86.KInv s₁ B R w R s₁ :=
    { hj := Nat.le_refl _
      esi := by rw [h₁.esi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rd := rfl
      wr := rfl
      keep := fun _ _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.keyLoop_ok hk hi₁) fun s₂ d₂ => ?_)
  have edi₂ : s₂.gpr .edi = B := (d₂.keep _ (by decide) (by decide)).trans h₁.edi
  have esp₂ : s₂.gpr .esp = E := (d₂.keep _ (by decide) (by decide)).trans h₁.esp
  have kfSub := hk.frame_sub
  have d₂' : ∀ {r : Region}, r.Disjoint (VG.Proof.Aes.X86.scrR s₀) → ∀ r' ∈ VG.Proof.Aes.X86.keyFrame B, r.Disjoint r' :=
    fun h r' hr' => h.sub_right (kfSub r' hr')
  have arg₂ : ∀ i < 6, s₂.mem.readW (addr E (4 + 4 * i)) 32 = VG.X86.arg s₀ i := fun i hi => by
    rw [← arg₁ i hi]; exact d₂.frame.readW (argC i hi) (d₂' hp.aB) (by decide)
  -- Between the loops.
  refine WP.seq (VG.Proof.Aes.X86.groupSetup_ok edi₂ esp₂ fB' (by rw [d₂.wr, h₁.wr]; exact hwB)
    (fun i hi => argIn _ (by rw [d₂.rd, h₁.rd]) i (by omega))
    (fun i hi => hp.aB.sub_left (VG.Proof.Aes.X86.part_sub (N := 28) (b := E) fSp (by omega) (by omega) (by omega)))
    fun s₃ edi₃ esp₃ g₃ ds₃ ns₃ z₃ F₃ rd₃ wr₃ => ?_)
  have F₃' : Frame [⟨addr B dOff, 8⟩] s₂.mem s₃.mem := F₃
  have d₃ : ∀ {r : Region}, r.Disjoint (VG.Proof.Aes.X86.scrR s₀) → ∀ r' ∈ [(⟨addr B dOff, 8⟩ : Region)], r.Disjoint r' :=
    fun h r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact h.sub_right (VG.Proof.Aes.X86.part_sub_reg fB (by decide))
  have arg₃ : ∀ i < 6, s₃.mem.readW (addr E (4 + 4 * i)) 32 = VG.X86.arg s₀ i := fun i hi => by
    rw [← arg₂ i hi]; exact F₃.readW (argC i hi) (d₃ hp.aB) (by decide)
  have e20 : s₂.mem.readW (addr E 20) 32 = VG.X86.arg s₀ 4 := arg₂ 4 (by omega)
  -- The regions the setup and the key loop wrote, all in the scratch buffer (or the counter).
  have hs : VG.Proof.Aes.X86.GSetup s₃ B D n R w icb :=
    { scr := by rw [wr₃, d₂.wr, h₁.wr]; exact hwB
      fitB := fB
      dat := by rw [wr₃, d₂.wr, h₁.wr]; exact hwD
      fitD := fD
      sep := hp.dDB
      rounds := hp.rounds
      argIn := by rw [esp₃]; exact argIn _ (by rw [rd₃, d₂.rd, h₁.rd]) 1 (by omega)
      argR := by rw [esp₃, arg₃ 1 (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      argSep := by rw [esp₃]; exact hp.aB.sub_left (VG.Proof.Aes.X86.part_sub (N := 28) (b := E) fSp (by omega) (by omega)
        (by omega))
      argSepD := by rw [esp₃]; exact hp.aD.sub_left (VG.Proof.Aes.X86.part_sub (N := 28) (b := E) fSp (by omega) (by omega)
        (by omega))
      keys := fun j hj => by
        refine keyRel_congr (d₂.keys j hj) fun k hk => ?_
        have := VG.Proof.Aes.X86.keyOff_le (j := j) hR'
        exact F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact VG.Proof.Aes.X86.part_disj fB (by simp only [lastKey] at this; omega) (by decide)
            (.inr (by simp only [dOff, lastKey] at this ⊢; omega))) (by decide)
      cw := fun v hv i hi j hj => by
        have e : VG.Proof.Aes.X86.cw s₃.mem B v = VG.Proof.Aes.X86.cw s₁.mem B v := by
          simp only [VG.Proof.Aes.X86.cw, cwOff]
          rw [F₃.readW (Region.contains_self _ _) (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact VG.Proof.Aes.X86.part_disj fB (by omega) (by decide) (.inl (by simp only [dOff]; omega))) (by decide)]
          exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
              rw [← VG.Proof.Aes.X86.addr_zero]; exact VG.Proof.Aes.X86.part_disj fB (by omega) (by omega) (.inr (by omega))
            · exact VG.Proof.Aes.X86.part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
        rw [e, h₁.cw v hv]; exact VG.Proof.Aes.X86.cw_bits _ fC hv hi hj }
  -- The memory the prologue, the key loop and the setup of the groups wrote.
  have dScr : ∀ {r : Region}, r.Disjoint (VG.Proof.Aes.X86.scrR s₀) → r.Disjoint (VG.Proof.Aes.X86.ctrR s₀) → ∀ {m' : Mem},
      Frame [⟨addr B dOff, 8⟩] s₂.mem m' → Frame [VG.Proof.Aes.X86.scrR s₀, VG.Proof.Aes.X86.ctrR s₀] s₀.mem m' := by
    intro r _ _ m' hf
    refine (F₁.sub fun r hr => ?_).trans ((d₂.frame.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.Aes.X86.scrR s₀, by simp, VG.Proof.Aes.X86.part_sub_reg fB (by omega)⟩
      · exact ⟨VG.Proof.Aes.X86.ctrR s₀, by simp, VG.Proof.Aes.X86.part_sub_reg fC (by omega)⟩
    · exact ⟨VG.Proof.Aes.X86.scrR s₀, by simp, kfSub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Aes.X86.scrR s₀, by simp, VG.Proof.Aes.X86.part_sub_reg fB (by decide)⟩
  have G₃ : Frame [VG.Proof.Aes.X86.scrR s₀, VG.Proof.Aes.X86.ctrR s₀] s₀.mem s₃.mem := dScr hp.dDB hp.dCD.symm F₃
  have num₃ : VG.Proof.Aes.X86.cnum s₃.mem B = icb.extractLsb' 0 32 := by
    rw [← VG.Proof.Aes.X86.icb_lo _ fC, ← h₁.cnum]
    simp only [VG.Proof.Aes.X86.cnum, cNum]
    rw [F₃.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Proof.Aes.X86.part_disj fB (by omega) (by decide) (.inl (by decide))) (by decide)]
    exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
        rw [← VG.Proof.Aes.X86.addr_zero]; exact VG.Proof.Aes.X86.part_disj fB (by omega) (by omega) (.inr (by omega))
      · exact VG.Proof.Aes.X86.part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
  have dD : ∀ r ∈ [VG.Proof.Aes.X86.scrR s₀, VG.Proof.Aes.X86.ctrR s₀], (VG.Proof.Aes.X86.datR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dDB
    · exact hp.dCD.symm
  have data₃ : VG.Proof.Aes.X86.DataInv s₀.mem s₃.mem (D.setWidth 64) n 0 (VG.Proof.Aes.X86.keyStream R w icb) := fun i hi => by
    rw [ite_eq_right (show ¬ i < 0 by omega)]
    exact (G₃.bytes (R := VG.Proof.Aes.X86.datR s₀) dD (by show 16 * n ≤ 2 ^ 64; omega) hi).trans (by simp; rfl)
  -- The groups.
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.X86.GDone s₀.mem s₃ B D n R w icb) ?_ fun s₄ h₄ => ?_)
  · refine WP.ite (VG.X86.arg s₀ 4 == 0) (by simp only [X86.eval, z₃, e20]) (fun hb => ?_) (fun hb => ?_)
    · have hn0 : n = 0 := by
        have : VG.X86.arg s₀ 4 = 0 := by simpa using hb
        show (VG.X86.arg s₀ 4).toNat = 0; rw [this]; rfl
      exact WP.block_nil ⟨edi₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
    · have hn0 : 0 < n := by
        have : VG.X86.arg s₀ 4 ≠ 0 := by simpa using hb
        show 0 < (VG.X86.arg s₀ 4).toNat
        exact Nat.pos_of_ne_zero fun h => this (BitVec.eq_of_toNat_eq (by simpa using h))
      refine VG.Proof.Aes.X86.groups_ok hs ⟨by omega, edi₃, rfl, rfl, rfl, Frame.refl _ _, by rw [num₃]; simp, ?_, ?_,
        by simpa using data₃⟩
      · rw [ds₃, arg₂ 3 (by omega)]; simp; rfl
      · rw [ns₃, e20, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · -- The epilogue.
    have G₄ : Frame [VG.Proof.Aes.X86.scrR s₀, VG.Proof.Aes.X86.ctrR s₀, VG.Proof.Aes.X86.datR s₀] s₀.mem s₄.mem := by
      refine (G₃.mono (by simp)).trans (h₄.frame.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Aes.X86.scrR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨VG.Proof.Aes.X86.scrR s₀, by simp, VG.Proof.Aes.X86.part_sub_reg fB (by decide)⟩
      · exact ⟨VG.Proof.Aes.X86.datR s₀, by simp, fun _ h => h⟩
    have retD : ∀ r ∈ [VG.Proof.Aes.X86.scrR s₀, VG.Proof.Aes.X86.ctrR s₀, VG.Proof.Aes.X86.datR s₀], (VG.Proof.Aes.X86.retR s₀).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.rB
      · exact hp.rC
      · exact hp.rD
    -- The saved registers.
    have saved : Spill.Saved s₄.mem (addr B) s₀.gpr savedRegs := fun p hp' => by
      have ho : 256 ≤ p.2 ∧ p.2 + 4 ≤ 272 := by revert p hp'; decide
      rw [← h₁.saved p hp']
      have e₄ : s₄.mem.readW (addr B p.2) 32 = s₃.mem.readW (addr B p.2) 32 :=
        h₄.frame.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
            rw [← VG.Proof.Aes.X86.addr_zero]; exact VG.Proof.Aes.X86.part_disj fB (by omega) (by omega) (.inr (by omega))
          · exact VG.Proof.Aes.X86.part_disj fB (by omega) (by decide) (.inl (by simp only [cNum]; omega))
          · exact (hp.dDB.sub_right (VG.Proof.Aes.X86.part_sub_reg fB (by omega))).symm) (by decide)
      rw [e₄, F₃.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact VG.Proof.Aes.X86.part_disj fB (by omega) (by decide) (.inl (by simp only [dOff]; omega))) (by decide)]
      exact d₂.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
          rw [← VG.Proof.Aes.X86.addr_zero]; exact VG.Proof.Aes.X86.part_disj fB (by omega) (by omega) (.inr (by omega))
        · exact VG.Proof.Aes.X86.part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
    have esp₄ : s₄.gpr .esp = E := h₄.esp.trans esp₃
    refine WP.mono (VG.Proof.Aes.X86.restore_ok h₄.base fB' (by rw [h₄.wr, wr₃, d₂.wr, h₁.wr]; exact hwB) saved)
      fun s₅ r₅ => ?_
    refine ⟨⟨r₅.abi (by decide) (by decide) esp₄, ?_⟩, ?_, ?_⟩
    · rw [r₅.mem]
      exact G₄.readW (Region.contains_self _ _) retD (by decide)
    · show Spec.Gcm.blocksAt s₅.mem (D.setWidth 64) n = _
      rw [r₅.mem]; exact VG.Proof.Aes.X86.ctr32_of_dataInv h₄.data
    · show Spec.Gcm.blockAt s₅.mem (C.setWidth 64) = Nat.repeat Spec.Gcm.inc32 n icb
      have e : Spec.Gcm.blockAt s₅.mem (C.setWidth 64) = Spec.Gcm.blockAt s₁.mem (C.setWidth 64) := by
        refine Proof.Gcm.blockAt_congr fun k hk => ?_
        rw [r₅.mem]
        have H : Frame [VG.Proof.Aes.X86.scrR s₀, VG.Proof.Aes.X86.datR s₀] s₁.mem s₄.mem := by
          refine (d₂.frame.sub fun r hr => ⟨VG.Proof.Aes.X86.scrR s₀, by simp, kfSub r hr⟩).trans
            ((F₃.sub fun r hr => ⟨VG.Proof.Aes.X86.scrR s₀, by simp, by
              simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Aes.X86.part_sub_reg fB (by decide)⟩).trans
            (h₄.frame.sub fun r hr => ?_))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨VG.Proof.Aes.X86.scrR s₀, by simp, Region.sub_prefix (by omega)⟩
          · exact ⟨VG.Proof.Aes.X86.scrR s₀, by simp, VG.Proof.Aes.X86.part_sub_reg fB (by decide)⟩
          · exact ⟨VG.Proof.Aes.X86.datR s₀, by simp, fun _ h => h⟩
        exact H.bytes (R := VG.Proof.Aes.X86.ctrR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hp.dCB
          · exact hp.dCD) (by show 16 ≤ 2 ^ 64; decide) hk
      rw [e]
      refine VG.Proof.Aes.X86.ctr_after fC (N := VG.X86.arg s₀ 4) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (fun k hk => ?_)
        h₁.ctr
      refine VG.Proof.Aes.X86.frame_one (r := ⟨addr C k, 1⟩) F₁ (Region.contains_self _ _) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.dCB.sub_left (VG.Proof.Aes.X86.part_sub_reg fC (by omega))).sub_right (VG.Proof.Aes.X86.part_sub_reg fB (by omega))
      · exact VG.Proof.Aes.X86.part_disj fC (N := 16) (by omega) (by omega) (.inl (by omega))

/-- Memory holding the arguments `0x1000, 10, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def ctrSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800D then 0x20
  else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0

/-- A state satisfying the precondition (with no data). -/
def ctrSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Aes.X86.ctrSatMem
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 24⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2048⟩]

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.ctr32 s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32X86.post s s' :=
  (VG.Proof.Aes.X86.correct (CPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem ctr32_verified :
    Verified X86.target Impl.Aes.X86.ctr32 (Spec.Gcm.ctr32Contract X86.abi) :=
  Verified.of_correct VG.Proof.Aes.X86.ctr32_correct VG.Proof.Aes.X86.ctr32_ct
    (by
      have a0 : VG.X86.arg VG.Proof.Aes.X86.ctrSat 0 = 0x1000 := by decide
      have a1 : VG.X86.arg VG.Proof.Aes.X86.ctrSat 1 = 10 := by decide
      have a2 : VG.X86.arg VG.Proof.Aes.X86.ctrSat 2 = 0x2000 := by decide
      have a3 : VG.X86.arg VG.Proof.Aes.X86.ctrSat 3 = 0x3000 := by decide
      have a4 : VG.X86.arg VG.Proof.Aes.X86.ctrSat 4 = 0 := by decide
      have a5 : VG.X86.arg VG.Proof.Aes.X86.ctrSat 5 = 0x4000 := by decide
      have e : argAddr VG.Proof.Aes.X86.ctrSat 0 = 0x8004 := by decide
      have esp : ctrSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.ctr32X86] [a0, a1, a2, a3, a4, a5, e, esp] using VG.Proof.Aes.X86.ctrSat)

end VG.Proof.Aes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.Decrypt`. -/
section

/-!
# Decrypting two blocks, bitsliced, on x86 (32-bit)

The inverse layers (`Impl/Aes/X86/Inv.lean`) are checked by evaluation as
the cipher's are (`Sbox.lean`, `Linear.lean`): the inverse S-box on the
truth tables of the 256 inputs against the specification's (`invSboxT`),
the linear layers over the lane domain. `decrypt2_ok` composes them: from
two blocks in slots `0 … 7` (`InRel`), with the bitsliced round keys in the
scratch buffer (`EncPre`), `decrypt2` leaves the two plaintexts, having
written only the first 256 bytes of the scratch buffer. The round loop's
invariant is the specification's `foldl` over the rounds done, with `kp`
stepping down from the last round key.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (invSbox roundKey invSubBytes invShiftRows invMixColumns addRoundKey invCipher)
open VG.X86.Wp (Upd wp_mov wp_ldm wp_addi wp_add wp_sub wp_subi wp_cmp sub_beq)

/-! ## The inverse S-box -/

def invSboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.slot j == some ((invSboxT VG.Proof.Aes.X86.inTs).getD j 0)

theorem invSbox_check :
    VG.X86.Straight.check (table 32 256) VG.Proof.Aes.X86.linCfg (fun _ => none) invSboxCode VG.Proof.Aes.X86.sboxEnv VG.Proof.Aes.X86.invSboxPost = true := by
  decide +kernel

/-- The inverse S-box, at every bit position of the words in slots `0 … 7`. -/
theorem invSbox_ok {s : State} (hok : Ok VG.Proof.Aes.X86.linCfg s) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p = (invSbox (bsByte (VG.Proof.Aes.X86.Q s) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ VG.Proof.Aes.X86.invSbox_check
  have hout : ∀ j < 8, e'.slot j = some ((invSboxT VG.Proof.Aes.X86.inTs).getD j 0) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simpa using this
  have key : ∀ p < 32, ∃ s', runBlock isa invSboxCode s = some s' ∧
      Post (TableRel p (bsByte (VG.Proof.Aes.X86.Q s) p).toNat) VG.Proof.Aes.X86.linCfg (fun _ => none) e' s s'
        (fun r => (invSboxCode.all fun i => i.dst != some r) = false) := by
    intro p hp
    have hc := (bsByte (VG.Proof.Aes.X86.Q s) p).isLt
    refine run (table_sound hp hc) hok ⟨(fun r a h => by cases h), fun k a _ h => ?_,
      (fun _ _ _ h => by cases h)⟩ he
    simp only [VG.Proof.Aes.X86.sboxEnv] at h
    split at h
    · rename_i hk8
      cases h
      simp only [TableRel, VG.Proof.Aes.X86.inT, testBit_tableOf, hc, decide_true, Bool.true_and,
        BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8, VG.Proof.Aes.X86.Q, VG.Proof.Aes.X86.linCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have hc := (bsByte (VG.Proof.Aes.X86.Q s) p).isLt
    have := p₁.rel.slot j _ (by simp [VG.Proof.Aes.X86.linCfg]; omega) (hout j hj)
    have hb : s''.gpr sb = s.gpr sb := p₁.base
    simp only [TableRel, VG.Proof.Aes.X86.linCfg, hb] at this
    rw [VG.Proof.Aes.X86.Q, hb, ← this, ← getLsbD_row _ _ hj, row_invSboxT _ hc, VG.Proof.Aes.X86.row_inTs hc]
    simp
  · have : (invSboxCode.all fun i => i.dst != some r) = true :=
      VG.Proof.Aes.X86.keeps_rest (by decide +kernel) r hr
    simp [this]

/-! ## The linear layers -/

theorem invShiftRows_check :
    VG.X86.Straight.check (lanes 32 8) VG.Proof.Aes.X86.linCfg (linExt 0) Impl.Aes.X86.invShiftRows (linEnv VG.Proof.Aes.X86.qIns)
      (linPost 64 8 (VG.Proof.Aes.X86.qOuts invSrG)) = true := by
  decide +kernel

theorem invMixColumns_check :
    VG.X86.Straight.check (lanes 32 8) VG.Proof.Aes.X86.linCfg (linExt 0) Impl.Aes.X86.invMixColumns (linEnv VG.Proof.Aes.X86.qIns)
      (linPost 64 8 (VG.Proof.Aes.X86.qOuts invMcG)) = true := by
  decide +kernel

theorem invShiftRows_ok {s : State} (hok : Ok VG.Proof.Aes.X86.linCfg s) :
    ∃ s', runBlock isa Impl.Aes.X86.invShiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p = (VG.Proof.Aes.X86.Q s j).getLsbD (invSrSrc p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.X86.q_linear VG.Proof.Aes.X86.invShiftRows_check (by decide) rfl
    (by decide +kernel) hok (VG.Proof.Aes.X86.Q s) (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.X86.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, invSrG, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_word _ _ _ (by simp only [invSrSrc]; omega)]

theorem invMixColumns_ok {s : State} (hok : Ok VG.Proof.Aes.X86.linCfg s) :
    ∃ s', runBlock isa Impl.Aes.X86.invMixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 32, (VG.Proof.Aes.X86.Q s' j).getLsbD p = termsXor (VG.Proof.Aes.X86.Q s) (invMcTerms j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ tmpRegs → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion VG.Proof.Aes.X86.linCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rest⟩ := VG.Proof.Aes.X86.q_linear VG.Proof.Aes.X86.invMixColumns_check (by decide) rfl
    (by decide +kernel) hok (VG.Proof.Aes.X86.Q s) (fun _ _ => rfl) (fun j hj => by simp [VG.Proof.Aes.X86.linCfg] at hj)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp, invMcG, xorBits_map]
  intro wt hwt
  obtain ⟨wk, -, rfl⟩ := List.mem_map.mp hwt
  exact Nat.mod_lt _ (by decide)

/-! ## The rounds -/

theorem keyOff_pred {R m : Nat} (h : 1 ≤ m) (hm : m ≤ R) (hR : R ≤ 14) (B : BitVec 32) :
    B + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R m) - 32 = B + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (m - 1)) := by
  have := VG.Proof.Aes.X86.keyOff_succ (R := R) (m := m - 1) (by omega) hR B
  rw [Nat.sub_add_cancel h] at this
  rw [← this, BitVec.add_sub_cancel]

/-- `sub kp, 32`. -/
theorem subKp_wp {s₀ s : State} {Q : State → Prop} (hc : VG.Proof.Aes.X86.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.X86.Ctx s₀ s' → s'.gpr kp = s.gpr kp - 32 → Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s → Q s') :
    WP isa (.block [subI kp 32]) s Q :=
  wp_subi fun s' u _ _ => WP.block_nil (h s' (hc.upd u (.inr rfl)) u.gpr
    (VG.Proof.Aes.X86.Q_congr (u.other _ (by decide)) u.mem))

/-- `kp :=` the last round key. -/
theorem kpLast_wp {s₀ s : State} {R : Nat} {Q : State → Prop} (hc : VG.Proof.Aes.X86.Ctx s₀ s)
    (h : ∀ s', VG.Proof.Aes.X86.Ctx s₀ s' → s'.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R R) →
      Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s → Q s') :
    WP isa (.block kpLast) s Q := by
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil ?_
  have c₂ := (hc.upd u₁ (.inr rfl)).upd u₂ (.inr rfl)
  refine h s₂ c₂ ?_ (VG.Proof.Aes.X86.Q_congr (c₂.base.trans hc.base.symm) (by rw [u₂.mem, u₁.mem]))
  rw [u₂.gpr, u₁.gpr, show s.gpr .edi = s₀.gpr sb from hc.base]
  simp [VG.Proof.Aes.X86.keyOff]

/-- `cmpFirst`: ZF is set when `kp` is at round key 1. -/
theorem cmpFirst_wp {s₀ s : State} {R m : Nat} {w : List Byte} {Q : State → Prop}
    (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s) (hm : m ≤ R)
    (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R m))
    (h : ∀ s', VG.Proof.Aes.X86.Ctx s₀ s' → s'.gpr kp = s.gpr kp → Proof.Aes.X86.Q s' = Proof.Aes.X86.Q s →
      s'.zf = some (decide (m = 1)) → Q s') :
    WP isa (.block cmpFirst) s Q := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 1 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esp) 8) 4 := by
    rw [hc.rd, hc.wr, hc.esp]; exact hp.argIn
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ _ => wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ => wp_add fun s₅ u₅ _ =>
    wp_add fun s₆ u₆ _ => wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_sub fun s₉ u₉ _ =>
    wp_cmp fun s₁₀ u₁₀ _ hz => WP.block_nil ?_
  have c₉ : VG.Proof.Aes.X86.Ctx s₀ s₉ := ((((((((hc.upd u₁ (.inl (by decide))).upd u₂ (.inl (by decide))).upd u₃
    (.inl (by decide))).upd u₄ (.inl (by decide))).upd u₅ (.inl (by decide))).upd u₆
    (.inl (by decide))).upd u₇ (.inl (by decide))).upd u₈ (.inl (by decide))).upd u₉ (.inl (by decide))
  have hk₉ : s₉.gpr kp = s.gpr kp := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  have c₁₀ : VG.Proof.Aes.X86.Ctx s₀ s₁₀ := c₉.step u₁₀.rd u₁₀.wr (fun r _ _ => by rw [u₁₀.gpr])
    (by rw [u₁₀.mem]; exact Frame.refl _ _)
  refine h s₁₀ c₁₀ (by rw [u₁₀.gpr, hk₉]) (VG.Proof.Aes.X86.Q_congr (c₁₀.base.trans hc.base.symm)
    (by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])) ?_
  have e6 : s₆.gpr .ebx = BitVec.ofNat 32 (32 * R) := by
    rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hp.arg hc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e7 : s₇.gpr .eax = s₀.gpr sb := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ← hc.base]; rfl
  have e9 : s₉.gpr .eax = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R 1) := by
    rw [u₉.gpr, u₈.gpr, u₈.other .ebx (by decide), u₇.other .ebx (by decide), e6, e7]
    simp only [VG.Proof.Aes.X86.keyOff, lastKey]
    bv_omega
  rw [hz, hk₉, hk, e9, VG.Proof.Aes.X86.sub_self_add, sub_beq (by simp only [VG.Proof.Aes.X86.keyOff, lastKey]; omega)
    (by simp only [VG.Proof.Aes.X86.keyOff, lastKey]; omega)]
  simp only [VG.Proof.Aes.X86.keyOff, lastKey]
  exact congrArg some (decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩)

/-- A middle round of the inverse cipher. -/
theorem invRound_ok {s₀ s : State} {R m : Nat} {w : List Byte} {T : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hc : VG.Proof.Aes.X86.Ctx s₀ s) (hk : s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (R - m)))
    (hm : m + 1 < R) (hbs : BsRel (VG.Proof.Aes.X86.Q s) T) :
    WP isa (.block invRoundBody) s fun s' => VG.Proof.Aes.X86.Ctx s₀ s' ∧
      s'.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (R - (m + 1))) ∧
      BsRel (VG.Proof.Aes.X86.Q s') (fun b => irnd R w m (T b)) ∧ s'.zf = some (decide (m + 2 = R)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  simp only [invRoundBody]
  repeat rw [WP.block_append_iff (M := isa)]
  refine VG.Proof.Aes.X86.subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
  rw [hk, VG.Proof.Aes.X86.keyOff_pred (by omega) (by omega) hR, show R - m - 1 = R - (m + 1) by omega] at hk₁
  have hbs₁ : BsRel (VG.Proof.Aes.X86.Q s₁) T := by rw [hq₁]; exact hbs
  refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
  have hbs₂ := bs_invShiftRows h₂ hbs₁
  refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
  have hbs₃ := bs_invSubBytes h₃ hbs₂
  refine VG.Proof.Aes.X86.ark_step hp hc₃ (j := R - (m + 1)) (by rw [hk₃, hk₂, hk₁]) (by omega) hbs₃
    fun s₄ hc₄ hk₄ hbs₄ => ?_
  refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.invMixColumns_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ hk₅ => ?_
  have hbs₅ := bs_invMixColumns h₅ hbs₄
  have hk₅' : s₅.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (R - (m + 1))) := by
    rw [hk₅, hk₄, hk₃, hk₂, hk₁]
  refine VG.Proof.Aes.X86.cmpFirst_wp hp hc₅ (by omega) hk₅' fun s₆ hc₆ hk₆ hq₆ hz₆ => ⟨hc₆, ?_, ?_, ?_⟩
  · rw [hk₆, hk₅']
  · rw [hq₆]
    intro b hb i hi
    rw [hbs₅ b hb i hi]
    simp only [irnd, show R - 1 - m = R - (m + 1) by omega]
  · rw [hz₆]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- Two blocks, from `InRel` to `InRel` of their decryptions. -/
theorem decrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : VG.Proof.Aes.X86.EncPre s₀ R w) (hin : InRel (VG.Proof.Aes.X86.Q s₀) S) :
    WP isa decrypt2 s₀ fun s => VG.Proof.Aes.X86.Ctx s₀ s ∧ InRel (VG.Proof.Aes.X86.Q s) (fun b => invCipher R w (S b)) := by
  have hR : R ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hR1 : 2 ≤ R := by rcases hp.rounds with h | h | h <;> omega
  let A : Nat → Spec.Aes.State := fun b => addRoundKey (S b) (roundKey w R)
  let Inv : Nat → State → Prop := fun n s => ∃ m, n = R - 1 - m ∧ m + 1 < R ∧ VG.Proof.Aes.X86.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R (R - m)) ∧
    BsRel (VG.Proof.Aes.X86.Q s) (fun b => invMid R w m (A b))
  let Mid : State → Prop := fun s => VG.Proof.Aes.X86.Ctx s₀ s ∧
    s.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (VG.Proof.Aes.X86.keyOff R 1) ∧
    BsRel (VG.Proof.Aes.X86.Q s) (fun b => invMid R w (R - 1) (A b))
  refine WP.seq (WP.mono (Q := Inv (R - 1)) ?_ fun s h => WP.seq (WP.mono (Q := Mid) ?_ fun s h => ?_))
  · -- ortho, the last round key.
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.toBs_ok ((Ctx.refl s₀).linOk hp)) (Ctx.refl s₀) fun s₁ hc₁ h₁ _ => ?_
    have hbs₁ := bs_of_in h₁ hin
    refine VG.Proof.Aes.X86.kpLast_wp (R := R) hc₁ fun s₂ hc₂ hk₂ hq₂ => ?_
    have hbs₂ : BsRel (VG.Proof.Aes.X86.Q s₂) S := by rw [hq₂]; exact hbs₁
    exact VG.Proof.Aes.X86.ark_step hp hc₂ hk₂ (Nat.le_refl R) hbs₂ fun s₃ hc₃ hk₃ hbs₃ =>
      ⟨0, by omega, by omega, hc₃, by rw [hk₃, hk₂, Nat.sub_zero], hbs₃⟩
  · -- The middle rounds.
    refine WP.loop (M := isa) Inv (fun n s hs => ?_) (R - 1) s h
    obtain ⟨m, rfl, hm, hc, hk, hbs⟩ := hs
    refine WP.mono (VG.Proof.Aes.X86.invRound_ok hp hc hk hm hbs) fun s' ⟨hc', hk', hbs', hz⟩ => ?_
    by_cases hlast : m + 2 = R
    · refine .inl ⟨by simp [X86.eval, hz, hlast], hc', ?_, ?_⟩
      · rw [hk']; congr 3; omega
      · rw [show R - 1 = m + 1 by omega]
        intro b hb i hi
        rw [hbs' b hb i hi]; simp only [invMid_succ]
    · refine .inr ⟨by simp [X86.eval, hz, hlast], R - 1 - (m + 1), by omega, m + 1, rfl, by omega,
        hc', hk', fun b hb i hi => by rw [hbs' b hb i hi]; simp only [invMid_succ]⟩
  · -- The last round, and back to blocks.
    obtain ⟨hc, hk, hbs⟩ := h
    rw [WP.block_append_iff (M := isa)]
    simp only [invLastRound]
    repeat rw [WP.block_append_iff (M := isa)]
    refine VG.Proof.Aes.X86.subKp_wp hc fun s₁ hc₁ hk₁ hq₁ => ?_
    rw [hk, VG.Proof.Aes.X86.keyOff_pred (by omega) (by omega) hR] at hk₁
    have hbs₁ : BsRel (VG.Proof.Aes.X86.Q s₁) (fun b => invMid R w (R - 1) (A b)) := by rw [hq₁]; exact hbs
    refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.invShiftRows_ok (hc₁.linOk hp)) hc₁ fun s₂ hc₂ h₂ hk₂ => ?_
    have hbs₂ := bs_invShiftRows h₂ hbs₁
    refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.invSbox_ok (hc₂.linOk hp)) hc₂ fun s₃ hc₃ h₃ hk₃ => ?_
    have hbs₃ := bs_invSubBytes h₃ hbs₂
    refine VG.Proof.Aes.X86.ark_step hp hc₃ (j := 0) (by rw [hk₃, hk₂, hk₁]) (Nat.zero_le R) hbs₃ fun s₄ hc₄ _ hbs₄ => ?_
    refine VG.Proof.Aes.X86.layer_wp (VG.Proof.Aes.X86.fromBs_ok (hc₄.linOk hp)) hc₄ fun s₅ hc₅ h₅ _ => ⟨hc₅, ?_⟩
    have := in_of_bs h₅ hbs₄
    intro b hb i hi j hj
    rw [this b hb i hi j hj]; simp only [invCipher_eq]; rfl

end VG.Proof.Aes.X86

end
