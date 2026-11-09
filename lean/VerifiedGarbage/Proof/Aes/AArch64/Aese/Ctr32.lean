module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
meta import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Contract

/-!
# AES counter mode with the Armv8 Cryptographic Extension

`ctr32_correct` and `ctr32_ct` prove `Impl.Aes.AArch64.Aese.ctr32` against
`Proof.Aes.ctr32AArch64` (the contract `vg_aes_ctr32` is proven against), and
`ctr32To_correct` and `ctr32To_ct` its out-of-place form (`ctr32To`) against
`Proof.Aes.ctr32ToAArch64`: one proof (`correct`) of `ctr32Gen to` for both,
whose output is `op s₀ to`, the data itself in place.

`ctrs_ok`: `ctrs regs i` puts the counter blocks `inc₃₂^(c+i)(CB)`, … into
the registers `regs`; `xorData_ok`: `xorData to regs j` XORs them, encrypted,
into the data blocks and stores them to the output; both for any list of
registers, by induction. The loops keep, after `c` blocks, the counter
`c₀ + c` in `w10` and the first `c` output blocks written (`DataInvM`).
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.Aese

open VG VG.AArch64
open VG.Impl.Aes.AArch64.Aese
open VG.Spec.Aes (cipher)

/-! ## Instructions -/

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 128)) := by
  simp only [exec, addr, show off % 16 = 0 ∧ off < 4096 * 16 from ho, and_self, ite_true,
    Option.bind_some, State.load, h, Option.map_some, Mem.readW]
  rfl

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show off % 16 = 0 ∧ off < 4096 * 16 from ho, and_self, ite_true,
    Option.bind_some, State.store, h]

theorem inRegions_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Bytes of vectors -/

theorem setLane_bit_lo (x : BitVec 128) (v : BitVec 32) {j t : Nat} (h : j < 12) (ht : t < 8) :
    (setLane x 32 3 v).getLsbD (8 * j + t) = x.getLsbD (8 * j + t) := by
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp (disch := omega) only [decide_eq_true, Bool.not_true, Bool.not_false, Bool.and_false,
    Bool.and_true, Bool.false_and, Bool.true_and, Bool.or_false]

theorem setLane_bit_hi (x : BitVec 128) (v : BitVec 32) {j t : Nat} (h : ¬ j < 12) (hj : j < 16)
    (ht : t < 8) : (setLane x 32 3 v).getLsbD (8 * j + t) = v.getLsbD (8 * (j - 12) + t) := by
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.not_true, Bool.not_false,
    Bool.and_false, Bool.and_true, Bool.true_and, Bool.false_or]
  exact congrArg _ (by omega)

theorem vbyte_setLane (x : BitVec 128) (v : BitVec 32) {j : Nat} (hj : j < 16) :
    vbyte (setLane x 32 3 v) j = if j < 12 then vbyte x j else v.extractLsb' (8 * (j - 12)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  by_cases h : j < 12
  · rw [ite_eq_left h]
    simp only [vbyte, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and]
    exact setLane_bit_lo x v h ht
  · rw [ite_eq_right h]
    simp only [vbyte, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and]
    exact setLane_bit_hi x v h hj ht

theorem exec_addImm_w {s : State} {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .w d n imm) s = some (s.write .w d (s.read .w n + BitVec.ofNat _ imm)) := by
  simp [exec, h]

theorem rev32_byte (v : BitVec 32) {q : Nat} (hq : q < 4) :
    (rev32 v).extractLsb' (8 * q) 8 = v.extractLsb' (8 * (3 - q)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', rev32_bit v hq ht]

/-- A counter block in a register, as an AES state. -/
theorem ctrVec_st (m : Mem) (p : Addr) (k : Nat) :
    st (setLane (m.readW (p + BitVec.ofNat 64 0) 128) 32 3
      (rev32 ((Spec.Gcm.blockAt m p).extractLsb' 0 32 + BitVec.ofNat 32 k))) =
      ctrState (Spec.Gcm.blockAt m p) k := by
  apply st_ext; intro j hj
  rw [getD_st _ hj, ctrState, getD_ofFn hj, ctrBlock_byte _ _ hj, vbyte_setLane _ _ hj]
  by_cases h : j < 12
  · rw [ite_eq_left h, ite_eq_left h, vbyte_readW _ _ hj, toBytes_blockAt _ _ hj, BitVec.add_zero]
  · rw [ite_eq_right h, ite_eq_right h, rev32_byte _ (by omega),
      show 3 - (j - 12) = 15 - j by omega]

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by simp

/-! ## The counter blocks -/

/-- `s'` is `s` but for the registers `gs` and the vector registers `vs`. -/
structure Fr (gs : List Reg) (vs : List VReg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ gs → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ vs → s'.v r = s.v r
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Fr.refl (gs : List Reg) (vs : List VReg) (s : State) : Fr gs vs s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Fr.trans {gs : List Reg} {vs : List VReg} {s s' s'' : State} (h : Fr gs vs s s')
    (h' : Fr gs vs s' s'') : Fr gs vs s s'' :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), fun r hr => (h'.v r hr).trans (h.v r hr),
    h'.sp.trans h.sp, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Fr.mono {gs gs' : List Reg} {vs vs' : List VReg} {s s' : State} (h : Fr gs vs s s')
    (hg : ∀ r ∈ gs, r ∈ gs') (hv : ∀ r ∈ vs, r ∈ vs') : Fr gs' vs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hg r h'), fun r hr => h.v r fun h' => hr (hv r h'),
    h.sp, h.mem, h.rd, h.wr⟩

/-- The counter block `C + i` into `b`, `C` the counter in `w10`. -/
theorem ctr1_ok (b : VReg) (i : Nat) (s : State) (hi : i < 4096)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 16) :
    WP isa (.block (ctr1 b i)) s fun s' =>
      s'.v b = setLane (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128) 32 3
        (rev32 (s.read .w .x10 + BitVec.ofNat 32 i)) ∧ Fr [.x12] [b] s s' := by
  rw [ctr1, WP.block_cons_iff]
  refine ⟨_, exec_addImm_w hi, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldrq (off := 0) (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp [State.setV, State.write, State.read, sw32]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]

/-- The counter block `C + i`, as `ctr1` builds it. -/
abbrev ctrVec (m : Mem) (p : Addr) (C : BitVec 32) (i : Nat) : BitVec 128 :=
  setLane (m.readW (p + BitVec.ofNat 64 0) 128) 32 3 (rev32 (C + BitVec.ofNat 32 i))

theorem ctrs_ok : ∀ (regs : List VReg) (i : Nat) (s : State), regs.Nodup → i + regs.length ≤ 4096 →
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 16 →
    WP isa (.block (ctrs regs i)) s fun s' =>
      (∀ k (h : k < regs.length), s'.v regs[k] = ctrVec s.mem (s.gpr .x2) (s.read .w .x10) (i + k)) ∧
      Fr [.x12] regs s s'
  | [], _, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Fr.refl _ _ _⟩
  | b :: bs, i, s, hnd, hi, hin => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hi
    rw [ctrs, WP.block_append_iff]
    refine WP.mono (ctr1_ok b i s (by omega) hin) fun s₁ ⟨e₁, f₁⟩ => ?_
    have h2 : s₁.gpr .x2 = s.gpr .x2 := f₁.gpr _ (by decide)
    have h10 : s₁.read .w .x10 = s.read .w .x10 := by
      simp only [State.read, f₁.gpr _ (by decide : Reg.x10 ∉ [Reg.x12])]
    refine WP.mono (ctrs_ok bs (i + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega)
      (by rw [f₁.rd, f₁.wr, h2]; exact hin)) fun s' ⟨e, f⟩ => ⟨?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [f.v _ hbs, e₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk), f₁.mem, h2, h10, show i + 1 + k = i + (k + 1) by omega]
    · refine (f₁.mono (fun r h => h) (fun r h => by simp_all)).trans
        (f.mono (fun r h => h) (fun r h => List.mem_cons_of_mem _ h))

/-! ## The data -/

/-- XOR `b` and the block at `x3 + 16 j`, stored at `outR to + 16 j`. -/
theorem xor1_ok (to : Bool) (b : VReg) (j : Nat) (s : State) (hb : b ≠ .v31) (hj : j < 4096)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * j)) 16)
    (hout : InRegions s.wr (s.gpr (outR to) + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block (xor1 to b j)) s fun s' =>
      s'.mem = s.mem.write (s.gpr (outR to) + BitVec.ofNat 64 (16 * j)) 16
        (s.v b ^^^ s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (16 * j)) 128) ∧
      s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .v31 → s'.v r = s.v r) := by
  rw [xor1, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega) hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_strq (by omega) hout, WP.block_nil ?_⟩
  refine ⟨?_, rfl, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setV, h1, h2]⟩
  simp [State.setV, hb]

theorem xorData_ok {m₀ : Mem} {D O : Addr} {n c : Nat} {ks : Nat → Byte} (to : Bool)
    (hn : 16 * n < 2 ^ 64) (hDO : O = D ∨ Region.Disjoint ⟨D, 16 * n⟩ ⟨O, 16 * n⟩) :
    ∀ (regs : List VReg) (j : Nat) (s : State), regs.Nodup → .v31 ∉ regs →
    s.gpr .x3 = D + BitVec.ofNat 64 (16 * c) → s.gpr (outR to) = O + BitVec.ofNat 64 (16 * c) →
    j + regs.length ≤ 4096 → c + j + regs.length ≤ n →
    (⟨D, 16 * n⟩ : Region) ∈ s.rd ++ s.wr → (⟨O, 16 * n⟩ : Region) ∈ s.wr →
    Frame [⟨O, 16 * n⟩] m₀ s.mem → DataInvM m₀ s.mem D O n (c + j) ks →
    (∀ k (h : k < regs.length), ∀ t < 16, vbyte (s.v regs[k]) t = ks (16 * (c + j + k) + t)) →
    WP isa (.block (xorData to regs j)) s fun s' =>
      DataInvM m₀ s'.mem D O n (c + j + regs.length) ks ∧ Frame [⟨O, 16 * n⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .v31 → r ∉ regs → s'.v r = s.v r)
  | [], _, s, _, _, _, _, _, _, _, _, _, hD, _ =>
    WP.block_nil ⟨hD, Frame.refl _ _, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, h31, hx3, hxo, hj, hc, hr, hw, hf, hD, hks => by
    have hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h31' : .v31 ∉ bs := fun h => h31 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hj hc
    have ha : s.gpr .x3 + BitVec.ofNat 64 (16 * j) = D + BitVec.ofNat 64 (16 * (c + j)) := by
      rw [hx3, Offset.add_add_eq D (show 16 * c + 16 * j = 16 * (c + j) by omega)]
    have ho : s.gpr (outR to) + BitVec.ofNat 64 (16 * j) = O + BitVec.ofNat 64 (16 * (c + j)) := by
      rw [hxo, Offset.add_add_eq O (show 16 * c + 16 * j = 16 * (c + j) by omega)]
    rw [xorData, WP.block_append_iff]
    refine WP.mono (xor1_ok to b j s hb31 (by omega)
        (by rw [ha]; exact ⟨_, hr, Offset.contains_base D (by omega) (by omega)⟩)
        (by rw [ho]; exact ⟨_, hw, Offset.contains_base O (by omega) (by omega)⟩))
      fun s₁ ⟨m₁, g₁, sp₁, rd₁, wr₁, v₁⟩ => ?_
    rw [ha, ho] at m₁
    have hst := dataInvM_store1 hn (by omega) hD
      (v := s.v b ^^^ s.mem.readW (D + BitVec.ofNat 64 (16 * (c + j))) 128) fun t ht => by
        have := hks 0 (by simp) t ht
        simp only [List.getElem_cons_zero, Nat.add_zero] at this
        rw [vbyte_xor, vbyte_readW _ _ ht,
          Offset.add_add_eq D (show 16 * (c + j) + t = 16 * (c + j) + t from rfl),
          src_keep (m₃ := m₀) (j := 0) hDO hn (fun _ _ _ => rfl) hf hD _ (by omega) (by omega) (by omega),
          this]
    rw [← m₁] at hst
    refine WP.mono (xorData_ok (m₀ := m₀) (c := c) (ks := ks) to hn hDO bs (j + 1) s₁
      (List.nodup_cons.mp hnd).2 h31' (by rw [g₁]; exact hx3) (by rw [g₁]; exact hxo) (by omega)
      (by omega) (by rw [rd₁, wr₁]; exact hr) (by rw [wr₁]; exact hw) (hf.trans hst.2)
      (by rw [show c + (j + 1) = c + j + 1 by omega]; exact hst.1) (fun k hk t ht => by
        rw [v₁ _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h31' (h ▸ List.getElem_mem hk))]
        have := hks (k + 1) (by simp; omega) t ht
        simp only [List.getElem_cons_succ] at this
        rw [this, show c + j + (k + 1) = c + (j + 1) + k by omega]))
      fun s' ⟨d', f', g', sp', rd', wr', v'⟩ => ⟨?_, hst.2.trans f', g'.trans g₁, sp'.trans sp₁,
        rd'.trans rd₁, wr'.trans wr₁, fun r h1 h2 => ?_⟩
    · rw [List.length_cons, show c + j + (bs.length + 1) = c + (j + 1) + bs.length by omega]; exact d'
    · simp only [List.mem_cons, not_or] at h2
      rw [v' r h1 h2.2, v₁ r h2.1 h1]

/-! ## The precondition and the loop invariant -/

section
variable (s₀ : State)

abbrev kp : Addr := s₀.gpr .x0
abbrev nr : Nat := (s₀.gpr .x1).toNat
abbrev cp : Addr := s₀.gpr .x2
abbrev dp : Addr := s₀.gpr .x3
abbrev nb : Nat := (s₀.gpr .x4).toNat
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (kp s₀) (16 * (nr s₀ + 1))
/-- The initial counter block, and its counter. -/
abbrev cb : Spec.Gcm.Block := Spec.Gcm.blockAt s₀.mem (cp s₀)
abbrev c0 : BitVec 32 := (cb s₀).extractLsb' 0 32
/-- The keystream, byte by byte. -/
abbrev kst : Nat → Byte := keyStream (nr s₀) (sch s₀) (cb s₀)

variable (to : Bool)

/-- The output: the data in place, `x6`'s blocks out of place. -/
abbrev op : Addr := s₀.gpr (cond to .x6 .x3)
abbrev oR : Region := ⟨op s₀ to, 16 * nb s₀⟩

end

/-- The precondition of both contracts, `ctr32AArch64` in place and
`ctr32ToAArch64` out of place (`to`). -/
structure Pre (to : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = ⟨kp s₀, 240⟩ :: cond to [dR s₀] []
  wr : s₀.wr = [⟨cp s₀, 16⟩, oR s₀ to, ⟨s₀.gpr .x5, 2048⟩]
  s_c : Region.Disjoint ⟨kp s₀, 240⟩ ⟨cp s₀, 16⟩
  c_o : Region.Disjoint ⟨cp s₀, 16⟩ (oR s₀ to)
  /-- Out of place, the data and the output do not overlap. -/
  src : to = true → (dR s₀).Disjoint (oR s₀ to)
  wrap : (dp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64
  wrapO : (op s₀ to).toNat + 16 * nb s₀ ≤ 2 ^ 64
  rounds : nr s₀ = 10 ∨ nr s₀ = 12 ∨ nr s₀ = 14

theorem pre_of {s₀ : State} (h : Proof.Aes.ctr32AArch64.pre s₀) : Pre false s₀ := by
  obtain ⟨h1, h2, h3, _, _, h6, _, _, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h6, fun h => Bool.noConfusion h, h9, h9, h10⟩

theorem preTo_of {s₀ : State} (h : Proof.Aes.ctr32ToAArch64.pre s₀) : Pre true s₀ := by
  obtain ⟨h1, h2, h3, _, _, _, h7, _, h9, _, _, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h7, fun _ => h9, h12, h13, h14⟩

namespace Pre
variable {to : Bool} {s₀ : State} (hp : Pre to s₀)
include hp

theorem nb16 : 16 * nb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega

theorem dat : dR s₀ ∈ s₀.rd ++ s₀.wr := by
  cases to with
  | false => rw [hp.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  | true => rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem out : oR s₀ to ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem dDO : op s₀ to = dp s₀ ∨ Region.Disjoint (dR s₀) (oR s₀ to) := by
  cases to with
  | false => exact .inl rfl
  | true => exact .inr (hp.src rfl)

theorem n16 : 16 * nb s₀ < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hc => hp.c_o (cp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (cp s₀ - op s₀ to).isLt
  omega

theorem ctr_in : InRegions (s₀.rd ++ s₀.wr) (cp s₀ + BitVec.ofNat 64 0) 16 :=
  ⟨⟨cp s₀, 16⟩, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem key_in {o : Nat} (h : o + 16 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (kp s₀ + BitVec.ofNat 64 o) 16 :=
  ⟨⟨kp s₀, 240⟩, by rw [hp.rd]; simp, Offset.contains_base _ h (by omega)⟩

/-- Memory that only differs from the initial memory in the output. -/
theorem cb_frame {m : Mem} (hf : Frame [oR s₀ to] s₀.mem m) : Spec.Gcm.blockAt m (cp s₀) = cb s₀ :=
  Proof.Gcm.blockAt_congr fun _ hk => hf.bytes (R := ⟨cp s₀, 16⟩)
    (by simp only [List.mem_singleton, forall_eq]; exact hp.c_o)
    (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

end Pre

/-- After `c` blocks, with `x3`, the output's pointer `outR to`, `x4` and the
counter at block `p`. -/
structure Inv (to : Bool) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  keys : Keys (nr s₀) (sch s₀) s
  x2 : s.gpr .x2 = cp s₀
  x3 : s.gpr .x3 = dp s₀ + BitVec.ofNat 64 (16 * p)
  xo : s.gpr (outR to) = op s₀ to + BitVec.ofNat 64 (16 * p)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (nb s₀ - p)
  x10 : s.read .w .x10 = c0 s₀ + BitVec.ofNat 32 p
  frame : Frame [oR s₀ to] s₀.mem s.mem
  data : DataInvM s₀.mem s.mem (dp s₀) (op s₀ to) (nb s₀) c (kst s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Keys.of_v {nr : Nat} {w : List Byte} {vs : List VReg} {s s' : State} (h : Keys nr w s)
    (hrs : BlockRegs vs) (hv : ∀ r, r ∉ vs → s'.v r = s.v r) (h6 : s'.gpr .x6 = s.gpr .x6)
    (h7 : s'.gpr .x7 = s.gpr .x7) : Keys nr w s' :=
  ⟨h.rounds, fun j hj => by rw [hv _ (hrs.kreg j)]; exact h.full j hj,
    by rw [hv _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl]; exact h.k29,
    by rw [hv _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl]; exact h.k30,
    by rw [h6]; exact h.x6, by rw [h7]; exact h.x7⟩

theorem Keys.of_fr {nr : Nat} {w : List Byte} {gs : List Reg} {vs : List VReg} {s s' : State}
    (h : Keys nr w s) (hf : Fr gs vs s s') (h6 : .x6 ∉ gs) (h7 : .x7 ∉ gs) (hrs : BlockRegs vs) :
    Keys nr w s' := h.of_v hrs hf.v (hf.gpr _ h6) (hf.gpr _ h7)

theorem regs_ok (rs : List VReg) (h : rs = regs8 ∨ rs = [.v0]) :
    BlockRegs rs ∧ .v31 ∉ rs ∧ BlockRegs (.v31 :: rs) := by
  rcases h with rfl | rfl <;> refine ⟨⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩⟩

theorem keyStream_eq {R c k t : Nat} {w : List Byte} {icb : Spec.Gcm.Block} (ht : t < 16) :
    keyStream R w icb (16 * (c + k) + t) = (cipher R w (ctrState icb (c + k))).getD t 0 := by
  rw [keyStream, show (16 * (c + k) + t) / 16 = c + k by omega,
    show (16 * (c + k) + t) % 16 = t by omega]

theorem outR_ne_x12 (to : Bool) : outR to ≠ .x12 := by cases to <;> decide

/-- The counter blocks, AES and the XOR into the output, for the blocks
`c … c + N - 1` (`N` the number of registers). -/
theorem blocks_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) (rs : List VReg)
    (hrs : rs = regs8 ∨ rs = [.v0]) (tail : List Instr) {Q : State → Prop} {c : Nat}
    (hc : c + rs.length ≤ nb s₀) {s : State} (hI : Inv to s₀ c c s)
    (hQ : ∀ s', Inv to s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrs rs 0)) (.seq (aes rs) (.block (xorData to rs 0 ++ tail)))) s Q := by
  obtain ⟨hbr, h31, hbr31⟩ := regs_ok rs hrs
  have hlen : rs.length ≤ 8 := by rcases hrs with rfl | rfl <;> decide
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 16 := by
    rw [hI.rd, hI.wr, hI.x2]; exact hp.ctr_in
  refine WP.seq (WP.mono (ctrs_ok rs 0 s hbr.1 (by omega) hin) fun s₁ ⟨e₁, f₁⟩ => ?_)
  have hK₁ := hI.keys.of_fr f₁ (by decide) (by decide) hbr
  refine WP.seq (WP.mono (aes_ok hbr hK₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < rs.length), ∀ t < 16,
      vbyte (s₂.v rs[k]) t = kst s₀ (16 * (c + 0 + k) + t) := by
    intro k h t ht
    show _ = keyStream _ _ _ _
    rw [Nat.add_zero, keyStream_eq ht, ← getD_st _ ht, e₂ _ (List.getElem_mem h), e₁ k h, hI.x10,
      hI.x2, ctrVec, c0, Nat.zero_add, BitVec.add_assoc, ← BitVec.ofNat_add, ← hp.cb_frame hI.frame,
      ctrVec_st]
  rw [WP.block_append_iff]
  refine WP.mono (xorData_ok (m₀ := s₀.mem) (D := dp s₀) (O := op s₀ to) (c := c) to hp.n16 hp.dDO
      rs 0 s₂ hbr.1 h31
      (by rw [f₂.gpr, f₁.gpr _ (by decide), hI.x3])
      (by rw [f₂.gpr, f₁.gpr _ (by simp [outR_ne_x12]), hI.xo]) (by omega) (by omega)
      (by rw [f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr]; exact hp.dat)
      (by rw [f₂.wr, f₁.wr, hI.wr]; exact hp.out)
      (by rw [f₂.mem, f₁.mem]; exact hI.frame)
      (by rw [f₂.mem, f₁.mem, Nat.add_zero]; exact hI.data) ks)
    fun s₃ ⟨d₃, fr₃, g₃, sp₃, rd₃, wr₃, v₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have g : ∀ r, r ≠ .x12 → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃, f₂.gpr, f₁.gpr r (by simp [hr])]
  refine ⟨by omega, ?_, by rw [g _ (by decide), hI.x2], by rw [g _ (by decide), hI.x3],
    by rw [g _ (outR_ne_x12 to), hI.xo],
    by rw [g _ (by decide), hI.x4], by simp only [State.read]; rw [g _ (by decide)]; exact hI.x10,
    by rw [hm₂] at fr₃; exact hI.frame.trans fr₃, by rw [Nat.add_zero] at d₃; exact d₃,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩
  refine (hK₁.of_v hbr f₂.v (by rw [f₂.gpr]) (by rw [f₂.gpr])).of_v hbr31 (fun r hr => ?_)
    (by rw [g₃]) (by rw [g₃])
  simp only [List.mem_cons, not_or] at hr
  exact v₃ r hr.1 hr.2

/-! ## The loop bodies -/

theorem ushr3 {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem eval_zero {s : State} {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    AArch64.eval (.zero .x r) s = some (decide (k = 0)) := by
  simp only [AArch64.eval, State.read, h, BitVec.setWidth_eq, Option.some.injEq]
  by_cases h0 : k = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h0]

theorem eval_nonzero {s : State} {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k)
    (hk : k < 2 ^ 64) : AArch64.eval (.nonzero .x r) s = some (!decide (k = 0)) := by
  have := eval_zero h hk
  simp only [AArch64.eval, Option.some.injEq] at this ⊢
  rw [bne, this]

/-- The output's pointer advanced by `k` bytes, out of place. -/
theorem advO_ok (to : Bool) (k : Nat) (hk : k < 4096) (s : State) :
    WP isa (.block (advO to k)) s fun s' =>
      (∀ r, r ≠ .x14 → s'.gpr r = s.gpr r) ∧ (to = true → s'.gpr .x14 = s.gpr .x14 + BitVec.ofNat 64 k) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases to with
  | false => exact WP.block_nil ⟨fun _ _ => rfl, fun h => Bool.noConfusion h, rfl, rfl, rfl, rfl⟩
  | true =>
    rw [advO, cond, WP.block_cons_iff]
    refine ⟨_, exec_addImm_x hk, WP.block_nil ⟨fun r hr => ?_, fun _ => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp [State.write, hr]
    · simp [State.write, State.read]

/-- `d` blocks on (`b = 16 d` bytes): the pointers, the count and the counter advanced. -/
theorem Inv.adv {to : Bool} {s₀ : State} {c p d b : Nat} {s s' : State} (hI : Inv to s₀ c p s)
    (hd : p + d ≤ nb s₀) (hb : b = 16 * d)
    (hg : ∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x10 → r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r)
    (h3 : s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 b)
    (ho : to = true → s'.gpr .x14 = s.gpr .x14 + BitVec.ofNat 64 b)
    (h4 : s'.gpr .x4 = s.gpr .x4 - BitVec.ofNat 64 d)
    (h10 : s'.read .w .x10 = s.read .w .x10 + BitVec.ofNat 32 d)
    (hv : s'.v = s.v) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv to s₀ c (p + d) s' := by
  have hp3 : s.gpr .x3 + BitVec.ofNat 64 b = dp s₀ + BitVec.ofNat 64 (16 * (p + d)) := by
    rw [hI.x3, hb]; exact Offset.add_add_eq _ (by omega)
  refine ⟨hI.le, hI.keys.of_v (vs := []) ⟨List.nodup_nil, by simp⟩ (fun r _ => by rw [hv])
    (hg _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (hg _ (by decide) (by decide) (by decide) (by decide) (by decide)),
    by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.x2,
    by rw [h3, hp3], ?_, ?_, by rw [h10, hI.x10, BitVec.add_assoc, BitVec.ofNat_add],
    by rw [hm]; exact hI.frame, by rw [hm]; exact hI.data, by rw [hrd, hI.rd], by rw [hwr, hI.wr]⟩
  · cases to with
    | false => exact (h3.trans hp3 :)
    | true =>
      have := hI.xo
      simp only [outR, cond] at this ⊢
      rw [ho rfl, this, hb]; exact Offset.add_add_eq _ (by omega)
  · rw [h4, hI.x4, Offset.ofNat_sub_ofNat (by omega), show nb s₀ - p - d = nb s₀ - (p + d) by omega]

theorem tail8_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {s : State}
    (hI : Inv to s₀ (c + 8) c s) :
    WP isa (.block (([.addImm .w .x10 .x10 8, .addImm .x .x3 .x3 128, .subImm .x .x4 .x4 8,
        .lsr .x .x13 .x4 3] : List Instr) ++ advO to 128)) s fun s' =>
      Inv to s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((nb s₀ - (c + 8)) / 8) := by
  have hn := hp.nb16
  rw [WP.block_append_iff]
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_w (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  refine WP.mono (advO_ok to 128 (by decide) _) fun s' ⟨g', o', v', m', rd', wr'⟩ => ⟨?_, ?_⟩
  · refine hI.adv (d := 8) (b := 128) hc rfl (fun r h3 h4 h10 h13 h14 => ?_) ?_ (fun ht => ?_) ?_ ?_
      v' m' rd' wr'
    · rw [g' r h14]; simp [State.write, h3, h4, h10, h13]
    · rw [g' _ (by decide)]; simp [State.write, State.read]
    · rw [o' ht]; simp [State.write, State.read]
    · rw [g' _ (by decide)]; simp [State.write, State.read]
    · simp only [State.read]; rw [g' _ (by decide)]; simp [State.write, State.read, sw32]
  · have h4 : BitVec.ofNat 64 (nb s₀ - c) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (nb s₀ - (c + 8)) := by
      rw [Offset.ofNat_sub_ofNat (by omega), show nb s₀ - c - 8 = nb s₀ - (c + 8) by omega]
    rw [g' _ (by decide)]
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x4]
    rw [h4, ushr3 (by omega)]

theorem tail1_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {c : Nat} (hc : c + 1 ≤ nb s₀) {s : State}
    (hI : Inv to s₀ (c + 1) c s) :
    WP isa (.block (([.addImm .w .x10 .x10 1, .addImm .x .x3 .x3 16, .subImm .x .x4 .x4 1] : List Instr) ++
      advO to 16)) s (Inv to s₀ (c + 1) (c + 1)) := by
  have hn := hp.nb16
  rw [WP.block_append_iff]
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_w (imm := 1) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine WP.mono (advO_ok to 16 (by decide) _) fun s' ⟨g', o', v', m', rd', wr'⟩ => ?_
  refine hI.adv (d := 1) (b := 16) hc rfl (fun r h3 h4 h10 _ h14 => ?_) ?_ (fun ht => ?_) ?_ ?_
    v' m' rd' wr'
  · rw [g' r h14]; simp [State.write, h3, h4, h10]
  · rw [g' _ (by decide)]; simp [State.write, State.read]
  · rw [o' ht]; simp [State.write, State.read]
  · rw [g' _ (by decide)]; simp [State.write, State.read]
  · simp only [State.read]; rw [g' _ (by decide)]; simp [State.write, State.read, sw32]

theorem body8_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {s : State}
    (hI : Inv to s₀ c c s) :
    WP isa (body8 to) s fun s' =>
      Inv to s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((nb s₀ - (c + 8)) / 8) :=
  blocks_ok hp regs8 (.inl rfl) _ hc hI fun _ hI' => tail8_ok hp hc hI'

theorem body1_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {c : Nat} (hc : c + 1 ≤ nb s₀) {s : State}
    (hI : Inv to s₀ c c s) : WP isa (body1 to) s (Inv to s₀ (c + 1) (c + 1)) :=
  blocks_ok hp [.v0] (.inr rfl) _ hc hI fun _ hI' => tail1_ok hp hc hI'

/-! ## The prologue and the epilogue -/

theorem kreg_inj : ∀ j < 13, ∀ i < 13, kreg j = kreg i → j = i := by decide

theorem kreg_ne (j : Nat) : kreg j ≠ .v29 ∧ kreg j ≠ .v30 := by
  unfold kreg; split <;> decide

/-- The first `k` round keys, into `kreg 0 … kreg (k − 1)`. -/
theorem loads_ok (s : State)
    (hin : ∀ j < 13, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * j)) 16) :
    ∀ k ≤ 13, WP isa (.block ((List.range k).map fun j => .ldrq (kreg j) .x0 (16 * j))) s fun s' =>
      (∀ j < k, s'.v (kreg j) = s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * j)) 128) ∧
      Fr [] ((List.range k).map kreg) s s'
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), Fr.refl _ _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (loads_ok s hin k (by omega)) fun s₁ ⟨e₁, f₁⟩ => ?_
    have g₀ : s₁.gpr .x0 = s.gpr .x0 := f₁.gpr _ (by simp)
    refine WP.of_runBlock ⟨_, by
      simp only [List.map_cons, List.map_nil, runBlock_cons]
      rw [exec_ldrq (by omega) (by rw [f₁.rd, f₁.wr, g₀]; exact hin k (by omega)), runStep_some,
        runBlock_nil], ?_⟩
    refine ⟨fun j hj => ?_, ⟨fun r _ => f₁.gpr r (by simp), fun r hr => ?_, f₁.sp, f₁.mem, f₁.rd,
      f₁.wr⟩⟩
    · by_cases hjk : j = k
      · subst hjk; rw [setV_v_self, f₁.mem, g₀]
      · rw [setV_v_of_ne _ _ fun h => hjk (kreg_inj j (by omega) k (by omega) h), e₁ j (by omega)]
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton,
        not_or] at hr
      rw [setV_v_of_ne _ _ hr.2, f₁.v r hr.1]

theorem exec_lsl_x {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.read .x n <<< sh)) := by
  simp [exec, Size.bits, h]

/-- Out of place, the destination moved from `x6` to `x14`. -/
theorem movO_ok (to : Bool) (s : State) :
    WP isa (.block (cond to [.addImm .x .x14 .x6 0] [])) s fun s' =>
      (∀ r, r ≠ .x14 → s'.gpr r = s.gpr r) ∧ (to = true → s'.gpr .x14 = s.gpr .x6) ∧
      s'.v = s.v ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases to with
  | false => exact WP.block_nil ⟨fun _ _ => rfl, fun h => Bool.noConfusion h, rfl, rfl, rfl, rfl⟩
  | true =>
    rw [cond, WP.block_cons_iff]
    refine ⟨_, exec_addImm_x (imm := 0) (by decide),
      WP.block_nil ⟨fun r hr => ?_, fun _ => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp [State.write, hr]
    · simp [State.write, State.read]

theorem setup_ok {to : Bool} {s₀ s : State} (hp : Pre to s₀) (hg : ∀ r, r ≠ .x14 → s.gpr r = s₀.gpr r)
    (ho : to = true → s.gpr .x14 = s₀.gpr .x6) (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    WP isa (.block setup) s fun s' => Inv to s₀ 0 0 s' ∧ s'.gpr .x13 = BitVec.ofNat 64 (nb s₀ / 8) := by
  have hR := hp.rounds
  have hn := hp.nb16
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (nr s₀) := by simp [nr]
  rw [setup, WP.block_append_iff]
  refine WP.mono (loads_ok s (fun j hj => by
      rw [hrd, hwr, hg _ (by decide)]; exact hp.key_in (by omega)) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, r ≠ .x14 → s₁.gpr r = s₀.gpr r := fun r hr => (f₁.gpr r (by simp)).trans (hg r hr)
  have g0 := g .x0 (by decide)
  have g1 := g .x1 (by decide)
  have g2 := g .x2 (by decide)
  have g3 := g .x3 (by decide)
  have g4 := g .x4 (by decide)
  have g14 : s₁.gpr .x14 = s.gpr .x14 := f₁.gpr _ (by simp)
  have hm₁ : s₁.mem = s₀.mem := f₁.mem.trans hm
  have e₁' : ∀ j < 13, s₁.v (kreg j) = s₀.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 (16 * j)) 128 :=
    fun j hj => by rw [e₁ j hj, hm, hg _ (by decide)]
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀) := by
    rw [g0, g1, shl4]
  have e9' : kp s₀ + BitVec.ofNat 64 (16 * nr s₀) - BitVec.ofNat 64 16 =
      kp s₀ + BitVec.ofNat 64 (16 * (nr s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega), show 16 * nr s₀ - 16 = 16 * (nr s₀ - 1) by omega]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr, hrd, hwr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact hp.key_in (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, e9', BitVec.add_zero, rdwr]
    exact hp.key_in (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_w (off := 12) (by decide) (by
    simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false, rdwr, g2]
    exact ⟨⟨cp s₀, 16⟩, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ nr s₀ → 16 * j + 16 ≤ 16 * (nr s₀ + 1) := fun j hj => by omega
  have hx4 : s₀.gpr .x4 = BitVec.ofNat 64 (nb s₀) := by simp [nb]
  refine ⟨⟨Nat.zero_le _, ⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, (kreg_ne j).2, ite_false]
    rw [e₁' j (by omega)]
    exact keyIs_readW _ _ (hL j (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, e9', BitVec.add_zero, hm₁]
    exact keyIs_readW _ _ (hL _ (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, hm₁]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g1, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g1, hx1]; rfl
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, g2]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, g3, Nat.mul_zero, BitVec.add_zero]
  · cases to with
    | false => simp only [outR, cond, State.setV, State.write, reduceCtorEq, ite_false, g3, Nat.mul_zero,
        BitVec.add_zero]; rfl
    | true => simp only [outR, cond, State.setV, State.write, reduceCtorEq, ite_false, g14, ho rfl,
        Nat.mul_zero, BitVec.add_zero]; rfl
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, g4, Nat.sub_zero, hx4]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false, sw32, g2,
      hm₁, BitVec.add_zero]
    exact icb_lo _ _
  · show Frame [oR s₀ to] s₀.mem s₁.mem
    rw [hm₁]; exact Frame.refl _ _
  · intro i hi
    show s₁.mem _ = _
    rw [hm₁, ite_eq_right (by omega)]
  · exact f₁.rd.trans hrd
  · exact f₁.wr.trans hwr
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g4, hx4]
    exact ushr3 (by omega)

/-- What both contracts' postconditions say, of the output `op s₀ to`. -/
def Post (to : Bool) (s₀ s : State) : Prop :=
  Spec.Gcm.blocksAt s.mem (op s₀ to) (nb s₀) =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith (nr s₀) (sch s₀)) (cb s₀) (Spec.Gcm.blocksAt s₀.mem (dp s₀) (nb s₀)) ∧
    Spec.Gcm.blockAt s.mem (cp s₀) = Nat.repeat Spec.Gcm.inc32 (nb s₀) (cb s₀)

theorem ctrStore_ok {to : Bool} {s₀ : State} (hp : Pre to s₀) {s : State}
    (hI : Inv to s₀ (nb s₀) (nb s₀) s) : WP isa (.block ctrStore) s (Post to s₀) := by
  have hn := hp.n16
  have hw : InRegions s.wr (cp s₀ + BitVec.ofNat 64 12) 4 :=
    ⟨⟨cp s₀, 16⟩, by rw [hI.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [ctrStore, WP.block_cons_iff]; refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_str_w (off := 12) (by decide) (by
    simp only [State.write, reduceCtorEq, ite_false, hI.x2]; exact hw), WP.block_nil ?_⟩
  simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, hI.x2, sw32]
  rw [show BitVec.setWidth 32 (s.gpr .x10) = s.read .w .x10 from rfl, hI.x10]
  -- The counter word is outside the output.
  have hf : Frame [⟨cp s₀ + BitVec.ofNat 64 12, 4⟩] s.mem
      (s.mem.writeW (cp s₀ + BitVec.ofNat 64 12) (rev32 (c0 s₀ + BitVec.ofNat 32 (nb s₀)))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd : ∀ r ∈ [(⟨cp s₀ + BitVec.ofNat 64 12, 4⟩ : Region)], Region.Disjoint (oR s₀ to) r := by
    simp only [List.mem_singleton, forall_eq]
    exact hp.c_o.symm.sub_right (Offset.sub_base _ (by omega))
  refine ⟨ctr32_of_dataInvM (dataInvM_frame hf hd hn hI.data), ctr_after fun k hk => ?_⟩
  show (s.mem.writeW (cp s₀ + BitVec.ofNat 64 12) (rev32 (c0 s₀ + BitVec.ofNat 32 (nb s₀)))) _ = _
  rw [writeW_apply, off_toNat _ (by omega) (by omega)]
  by_cases h : 12 ≤ k
  · rw [ite_eq_left h, ite_eq_left (show k - 12 < 32 / 8 by omega), ite_eq_right (show ¬ k < 12 by omega),
      icb_lo, BitVec.setWidth_eq]
    congr 3
    apply BitVec.eq_of_toNat_eq; simp
  · rw [ite_eq_right h, ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega),
      ite_eq_left (show k < 12 by omega)]
    exact hI.frame.bytes (R := ⟨cp s₀, 16⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact hp.c_o) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

/-! ## The whole function -/

theorem correct {to : Bool} {s₀ : State} (hp : Pre to s₀) : WP isa (ctr32Gen to) s₀ (Post to s₀) := by
  have hn := hp.n16
  refine WP.seq (WP.mono (Q := fun (s : State) => Inv to s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (nb s₀ / 8))
    ?_ fun s₁ ⟨hI₁, h13⟩ => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (movO_ok to s₀) ?_
    rintro s ⟨hg, ho, _, hm, hrd, hwr⟩
    exact setup_ok hp hg ho hm hrd hwr
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nb s₀ - c < 8 ∧ Inv to s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (nb s₀ / 8 = 0)) (eval_zero h13 (by omega)) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simp at h; omega, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c + 8 ≤ nb s₀ ∧ Inv to s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (body8 to) s (fun s' =>
          (AArch64.eval (.nonzero .x .x13) s' = some false ∧ ∃ c, nb s₀ - c < 8 ∧ Inv to s₀ c c s') ∨
          (AArch64.eval (.nonzero .x .x13) s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body8_ok hp hc hI) fun s' ⟨hI', h13'⟩ => ?_
        rw [eval_nonzero h13' (by omega)]
        by_cases hlt : nb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp; omega, c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp; omega, nb s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I8 hstep (nb s₀) s₁ ⟨0, rfl, by simp at h; omega, hI₁⟩
  refine WP.seq (WP.mono (Q := Inv to s₀ (nb s₀) (nb s₀)) ?_ fun s₄ hI₄ => ctrStore_ok hp hI₄)
  refine WP.ite (decide (nb s₀ - c = 0)) (eval_zero hI₂.x4 (by omega)) (fun h => ?_) (fun h => ?_)
  · have : c = nb s₀ := by have := hI₂.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c < nb s₀ ∧ Inv to s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (body1 to) s (fun s' =>
        (AArch64.eval (.nonzero .x .x4) s' = some false ∧ Inv to s₀ (nb s₀) (nb s₀) s') ∨
        (AArch64.eval (.nonzero .x .x4) s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hc hI) fun s' hI' => ?_
      rw [eval_nonzero hI'.x4 (by omega)]
      by_cases hlast : nb s₀ - (c + 1) = 0
      · have : c + 1 = nb s₀ := by omega
        exact .inl ⟨by simp [hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [hlast], nb s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < nb s₀ := by have := hI₂.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (nb s₀ - c) s₂ ⟨c, rfl, hlt, hI₂⟩

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32AArch64.pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ :=
    WP.gprs (rs := preserved) (show WP isa ctr32 s (Post false s) from correct (pre_of hs))
      (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ctr32To_correct (s : State) (hs : Proof.Aes.ctr32ToAArch64.pre s) :
    ∃ t s', Exec isa ctr32To s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32ToAArch64.post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ :=
    WP.gprs (rs := preserved) (show WP isa ctr32To s (Post true s) from correct (preTo_of hs))
      (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32To_ct :
    ConstantTime isa Proof.Aes.ctr32ToAArch64.pre Proof.Aes.ctr32ToAArch64.pub ctr32To := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Aes.AArch64.Aese
