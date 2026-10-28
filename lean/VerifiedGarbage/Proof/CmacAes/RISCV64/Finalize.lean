module

public import VerifiedGarbage.Proof.CmacAes.RISCV64.Contract
public import VerifiedGarbage.Impl.CmacAes.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.CmacAes.RISCV64.Subkeys
import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Cmac.RISCV64.Dbl
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# AES-CMAC on RISC-V: `vg_cmac_aes_finalize`

The return address and `s1` saved at `svOf S` (`Spill.save_ok`), the last
block `Mₙ` XORed into the state as it is formed (`full_wp` for a complete
block, `partial_wp` for a partial one: `BPost`), the state enciphered in
place, and the registers restored: `CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, the MAC
(`Proof.Cmac.macFull_split`), as on PPC64LE
(`Proof/CmacAes/PPC64LE/Finalize.lean`), which forms `Mₙ` in the scratch
buffer first.
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.CmacAes.RISCV64
open VG.Proof.AesCbc.RISCV64 (CallPre blk_call in_rw savePtr_ok xorInto_wp encryptBlocks_noFrames)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.RISCV64 (dbl_wp wp_xori dbl_spec16)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  a0 : s₀.gpr .a0 = W
  a2 : s₀.gpr .a2 = St
  a3 : s₀.gpr .a3 = P
  a4 : (s₀.gpr .a4).toNat = L
  a5 : s₀.gpr .a5 = S
  a1 : (s₀.gpr .a1).toNat = R
  rd : s₀.rd = [⟨W, 272⟩, ⟨P, L⟩]
  wr : s₀.wr = [⟨St, 16⟩, ⟨S, 2176⟩]
  key_st : (⟨W, 272⟩ : Region).Disjoint ⟨St, 16⟩
  key_scr : (⟨W, 272⟩ : Region).Disjoint ⟨S, 2176⟩
  last_st : (⟨P, L⟩ : Region).Disjoint ⟨St, 16⟩
  last_scr : (⟨P, L⟩ : Region).Disjoint ⟨S, 2176⟩
  st_scr : (⟨St, 16⟩ : Region).Disjoint ⟨S, 2176⟩
  key_wrap : W.toNat + 272 ≤ 2 ^ 64
  st_wrap : St.toNat + 16 ≤ 2 ^ 64
  last_wrap : P.toNat + L ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeRISCV64.pre s₀) :
    FPre s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a5) (s₀.gpr .a4).toNat (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (bytesAt m (W + BitVec.ofNat 64 240) 16)
    (bytesAt m (W + BitVec.ofNat 64 256) 16) (bytesAt m P L)

/-- The values `finalize` saves: `t0` holds `svOf S`. -/
abbrev finG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (svOf S)).gpr

/-- The memory after saving `s1` and the return address. -/
abbrev finMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem (svOf S) (finG s₀ S) finSaved

theorem fin_bound : ∀ p ∈ finSaved, 16 ≤ p.2 ∧ p.2 + 8 ≤ 32 := by decide

/-- The slots, from `svOf S`. -/
abbrev finSlots (S : Addr) : Region := ⟨svOf S + BitVec.ofNat 64 16, 16⟩

/-- Saving the registers changes only their slots. -/
theorem finMem_frame (s₀ : State) (S : Addr) : Frame [finSlots S] s₀.mem (finMem s₀ S) :=
  Spill.saveMem_frame (lo := 16) (n := 16) fin_bound (by decide) _ _ _

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem FPre.slots_scr {S : Addr} : Region.Sub (finSlots S) ⟨S, 2176⟩ := svOf_sub S (by decide)

theorem FPre.key_sub {W : Addr} {d n : Nat} (h : d + n ≤ 272) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 272⟩ :=
  Offset.sub_base _ h

theorem FPre.fin_frame {s₀ : State} {St S : Addr} : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem (finMem s₀ S) :=
  (finMem_frame s₀ S).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨S, 2176⟩, by simp, FPre.slots_scr⟩

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R)
include hp

theorem FPre.rKey {s : State} (hr : s.rd = s₀.rd) {d n : Nat} (h : d + n ≤ 272) :
    ∃ r ∈ s.rd ++ s.wr, Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ r :=
  ⟨⟨W, 272⟩, by rw [hr, hp.rd]; simp, FPre.key_sub h⟩

theorem FPre.wSt {s : State} (hw : s.wr = s₀.wr) : ∃ r ∈ s.wr, Region.Sub ⟨St, 16⟩ r :=
  ⟨⟨St, 16⟩, by rw [hw, hp.wr]; simp, fun _ h => h⟩

/-- Bytes of the key, unchanged by writes to the state and the scratch buffer. -/
theorem FPre.key_frame {m m' : Mem} (hf : Frame [⟨St, 16⟩, ⟨S, 2176⟩] m m') {d n : Nat} (h : d + n ≤ 272) :
    bytesAt m' (W + BitVec.ofNat 64 d) n = bytesAt m (W + BitVec.ofNat 64 d) n := by
  have := hp.key_wrap
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.key_st.sub_left (FPre.key_sub h)
  · exact hp.key_scr.sub_left (FPre.key_sub h)

/-- The last bytes, unchanged likewise. -/
theorem FPre.last_frame {m m' : Mem} (hf : Frame [⟨St, 16⟩, ⟨S, 2176⟩] m m') :
    bytesAt m' P L = bytesAt m P L := by
  have := hp.last_wrap
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.last_st
  · exact hp.last_scr

/-- The last block, from the memory after saving the registers. -/
theorem FPre.mn_frame {m : Mem} (hf : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem m) : mn m W P L = mn s₀.mem W P L := by
  rw [mn, mn, hp.key_frame hf (by decide), hp.key_frame hf (by decide), hp.last_frame hf]

end

/-! ## Bytes -/

theorem getD_padded {xs : List Byte} {L : Nat} (hxs : xs.length = L) (hL : L < 16) {k : Nat} (hk : k < 16) :
    (xs ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1)).getD k 0 =
      if k < L then xs.getD k 0 else if k = L then 0x80 else 0 := by
  subst hxs
  rcases Nat.lt_trichotomy k xs.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨j, hj⟩ : ∃ j, k - xs.length = j + 1 := ⟨k - xs.length - 1, by omega⟩
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (show xs.length ≤ k by omega),
      hj, List.singleton_append, List.getElem?_cons_succ, Spec.Cmac.zeros, List.getElem?_replicate]
    simp only [show j < 16 - xs.length - 1 by omega, ite_true, Option.getD_some, show ¬ k < xs.length by omega,
      show k ≠ xs.length by omega, ite_false]

theorem length_mn (m : Mem) (W P : Addr) {L : Nat} (hL : L ≤ 16) : (mn m W P L).length = 16 := by
  unfold mn Spec.Cmac.lastBlock
  split
  · rename_i h
    rw [Proof.Cmac.bytesAt_length] at h
    simp [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, h]
  · rename_i h
    rw [Proof.Cmac.bytesAt_length] at h
    simp [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, Spec.Cmac.zeros]; omega

/-- Byte `k` of the last block. -/
theorem getD_mn (m : Mem) (W P : Addr) {L : Nat} (hL : L ≤ 16) {k : Nat} (hk : k < 16) :
    (mn m W P L).getD k 0 = m (W + BitVec.ofNat 64 (if L = 16 then 240 else 256) + BitVec.ofNat 64 k) ^^^
      (if k < L then m (P + BitVec.ofNat 64 k) else if k = L then 0x80 else 0) := by
  unfold mn Spec.Cmac.lastBlock
  rw [Proof.Cmac.bytesAt_length]
  split
  · rename_i h
    obtain rfl : L = 16 := h
    rw [Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length]) (by simp [Proof.Cmac.bytesAt_length]; exact hk),
      Proof.Cmac.getD_bytesAt _ _ hk, Proof.Cmac.getD_bytesAt _ _ hk]
    simp [hk]
  · rename_i h
    rw [Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length, Spec.Cmac.zeros]; omega)
      (by simp [Proof.Cmac.bytesAt_length]; exact hk), Proof.Cmac.getD_bytesAt _ _ hk,
      getD_padded (Proof.Cmac.bytesAt_length _ _ _) (by omega) hk]
    split
    · rw [Proof.Cmac.getD_bytesAt _ _ (by assumption)]
    · rfl

/-! ## Saving -/

/-- What the code before the branch leaves. -/
structure FA (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = St
  a3 : s.gpr .a3 = P
  a4 : s.gpr .a4 = BitVec.ofNat 64 L
  s1 : s.gpr .s1 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  mem : s.mem = finMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem finSave_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    WP isa (.block finSave) s₀ fun s => FA s₀ W St P S L s ∧ isa.eval (.zero .t1) s = some (decide (L = 16)) := by
  have hL := hp.len
  have h4 : s₀.gpr .a4 = BitVec.ofNat 64 L := by rw [← hp.a4]; apply BitVec.eq_of_toNat_eq; simp
  rw [finSave, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a5) fun s₁ e => ?_
  subst e
  rw [hp.a5, show finSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 finSaved from rfl]
  have t₀ : (s₀.write .t0 (svOf S)).gpr .t0 = svOf S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (svOf S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := finSaved) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := fin_bound p hp'
    have := pad_lt (S + BitVec.ofNat 64 2048)
    have := hp.scr_wrap
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  generalize ht : ({ (s₀.write .t0 (svOf S)) with
    mem := Spill.saveMem (s₀.write .t0 (svOf S)).mem ((s₀.write .t0 (svOf S)).gpr .t0)
      (s₀.write .t0 (svOf S)).gpr finSaved } : State) = t
  have memt : t.mem = finMem s₀ S := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  have spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₂ u₂ => wp_subi (imm := 16) (by decide) fun s₃ u₃ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr h1 => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), hp.a0]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide)]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), hp.a2]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), hp.a3]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), h4]
  · rw [u₃.other _ (by decide), u₂.gpr, gt _ (by decide), hp.a5]
  · obtain ⟨h0, h1', -⟩ := preserved_ne r hr
    rw [u₃.other _ h1', u₂.other _ h1, gt _ h0]
  · rw [u₃.mem, u₂.mem, memt]
  · rw [u₃.rd, u₂.rd, rdt]
  · rw [u₃.wr, u₂.wr, wrt]
  · rw [u₃.sp, u₂.sp, spt]
  · rw [eval_zero, u₃.gpr, u₂.other _ (by decide), gt _ (by decide), h4]
    congr 1
    by_cases h : L = 16
    · subst h; decide
    · have hne : BitVec.ofNat 64 L - BitVec.ofNat 64 16 ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show 16 < 2 ^ 64 by decide)] at this
        have h0 : (2 ^ 64 - 16 + L) % 2 ^ 64 = 0 := this.trans rfl
        omega
      rw [beq_eq_false_iff_ne.mpr hne]; simp [h]

/-! ## The last block -/

/-- What the branch on the length leaves: `C ⊕ Mₙ` in the state. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = W
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = St
  s1 : s.gpr .s1 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St, 16⟩] (finMem s₀ S) s.mem
  st : bytesAt s.mem St 16 = Spec.Cmac.xor (bytesAt s₀.mem St 16) (mn s₀.mem W P L)

/-- The state, unchanged by saving the registers. -/
theorem FPre.st_fin {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    bytesAt (finMem s₀ S) St 16 = bytesAt s₀.mem St 16 :=
  Proof.Cmac.bytesAt_frame16 (finMem_frame s₀ S) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.st_scr.sub_right FPre.slots_scr

/-- Byte `k` of `C ⊕ Mₙ`. -/
theorem getD_xor_mn (m : Mem) (St W P : Addr) {L : Nat} (hL : L ≤ 16) {k : Nat} (hk : k < 16) :
    (Spec.Cmac.xor (bytesAt m St 16) (mn m W P L)).getD k 0 = m (St + BitVec.ofNat 64 k) ^^^
      (m (W + BitVec.ofNat 64 (if L = 16 then 240 else 256) + BitVec.ofNat 64 k) ^^^
        (if k < L then m (P + BitVec.ofNat 64 k) else if k = L then 0x80 else 0)) := by
  rw [Proof.Cmac.getD_xor (by rw [Proof.Cmac.bytesAt_length, length_mn _ _ _ hL])
    (by rw [Proof.Cmac.bytesAt_length]; exact hk), Proof.Cmac.getD_bytesAt _ _ hk, getD_mn _ _ _ hL hk]

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (h : FA s₀ W St P S L s) : WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have kw := hp.key_wrap
  have hr : s.rd = s₀.rd := h.rd
  rw [full, List.append_assoc]
  refine xorInto_wp (P := St) (Q := P) (by decide) (by decide) (by decide) (by decide) h.a2 h.a3
    ⟨⟨P, 16⟩, by rw [h.rd, hp.rd]; simp, fun _ h => h⟩ (hp.wSt h.wr) hp.last_st.symm
    fun s₁ g₁ x₁ f₁ rd₁ wr₁ sp₁ => ?_
  simp only [List.cons_append]
  refine wp_addi (imm := 240) (by decide) fun s₂ u₂ => ?_
  rw [List.nil_append]
  refine xorInto_wp (P := St) (Q := W + BitVec.ofNat 64 240) (by decide) (by decide) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h.a2])
    (by rw [u₂.gpr, g₁ _ (by decide) (by decide), h.a0])
    (hp.rKey (s := s₂) (by rw [u₂.rd, rd₁, h.rd]) (by decide)) (hp.wSt (by rw [u₂.wr, wr₁, h.wr]))
    (hp.key_st.symm.sub_right (FPre.key_sub (by decide))) fun s₃ g₃ x₃ f₃ rd₃ wr₃ sp₃ => WP.block_nil ?_
  have g (r : Reg) (h3 : r ≠ .t3) (h4 : r ≠ .t4) (h5 : r ≠ .t5) : s₃.gpr r = s.gpr r := by
    rw [g₃ r h3 h4, u₂.other _ h5, g₁ r h3 h4]
  have fr : Frame [⟨St, 16⟩] s.mem s₃.mem := f₁.trans (by rw [← u₂.mem]; exact f₃)
  have hfm : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s.mem := by rw [h.mem]; exact FPre.fin_frame
  refine ⟨by rw [g _ (by decide) (by decide) (by decide), h.a0], by rw [g _ (by decide) (by decide) (by decide), h.a1],
    by rw [g _ (by decide) (by decide) (by decide), h.a2], by rw [g _ (by decide) (by decide) (by decide), h.s1],
    fun r hr h1 => ?_, by rw [rd₃, u₂.rd, rd₁, h.rd], by rw [wr₃, u₂.wr, wr₁, h.wr], by rw [sp₃, u₂.sp, sp₁, h.sp],
    by rw [← h.mem]; exact fr, ?_⟩
  · obtain ⟨-, -, -, h3, h4, h5, -⟩ := preserved_ne r hr
    rw [g r h3 h4 h5, h.keep r hr h1]
  · -- `(C ⊕ Mₙ*) ⊕ K1`, byte by byte.
    have k1 : bytesAt s₁.mem (W + BitVec.ofNat 64 240) 16 = bytesAt s₀.mem (W + BitVec.ofNat 64 240) 16 := by
      rw [hp.key_frame (f₁.mono (by simp)) (by decide), hp.key_frame hfm (by decide)]
    have lst : bytesAt s.mem P 16 = bytesAt s₀.mem P 16 := hp.last_frame hfm
    have st : bytesAt s.mem St 16 = bytesAt s₀.mem St 16 := by rw [h.mem, hp.st_fin]
    rw [x₃, u₂.mem, x₁, k1, lst, st]
    refine Proof.Cmac.ext16 (by simp [Spec.Cbc.xor, Proof.Cmac.bytesAt_length])
      (by rw [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, length_mn _ _ _ (by decide)]; rfl) fun k hk => ?_
    rw [getD_xor_mn _ _ _ _ (by decide) hk]
    simp only [Spec.Cbc.xor]
    rw [← Spec.Cmac.xor, Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length])
        (by simp [Proof.Cmac.bytesAt_length]; exact hk),
      Proof.Cmac.getD_bytesAt _ _ hk, ← Spec.Cmac.xor,
      Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length]) (by simp [Proof.Cmac.bytesAt_length]; exact hk),
      Proof.Cmac.getD_bytesAt _ _ hk, Proof.Cmac.getD_bytesAt _ _ hk]
    simp only [hk, ite_true]
    rw [Offset.add_add]
    simp only [BitVec.xor_assoc, BitVec.xor_comm (s₀.mem (P + BitVec.ofNat 64 k))]

/-! ### A partial last block -/

theorem cbc_xor : Spec.Cbc.xor = Spec.Cmac.xor := rfl

/-- After `i` bytes XORed into the state, from `s`. -/
structure XInv (s : State) (St P : Addr) (L i : Nat) (t : State) : Prop where
  le : i ≤ L
  t5 : t.gpr .t5 = P + BitVec.ofNat 64 i
  t6 : t.gpr .t6 = St + BitVec.ofNat 64 i
  t1 : t.gpr .t1 = BitVec.ofNat 64 (L - i)
  gpr : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  bytes : ∀ j < 16, t.mem (St + BitVec.ofNat 64 j) =
    if j < i then s.mem (P + BitVec.ofNat 64 j) ^^^ s.mem (St + BitVec.ofNat 64 j) else s.mem (St + BitVec.ofNat 64 j)
  frame : Frame [⟨St, 16⟩] s.mem t.mem

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R)
include hp

theorem xorStep_wp (hL : L < 16) {s : State} (hs : FA s₀ W St P S L s) {i : Nat} (hi : i < L) {t : State}
    (h : XInv s St P L i t) :
    WP isa (.block [.load .b .t3 .t5 0, .load .b .t4 .t6 0, .logic .xor .t3 .t3 .t4, .store .b .t3 .t6 0,
      .addi .t5 .t5 1, .addi .t6 .t6 1, .addi .t1 .t1 (-1)]) t (XInv s St P L (i + 1)) := by
  have sw := hp.st_wrap
  have lw := hp.last_wrap
  have hsep : ∀ j < 16, ¬ (⟨St, 16⟩ : Region).Contains (P + BitVec.ofNat 64 j) 1 → True := fun _ _ _ => trivial
  have pS : ¬ (⟨St, 16⟩ : Region).Contains (P + BitVec.ofNat 64 i) 1 := fun hc =>
    hp.last_st _ (Offset.contains_base _ (by omega) (by omega)) hc
  refine wp_lbu (a := P + BitVec.ofNat 64 i) (by decide) (by rw [h.t5, BitVec.add_zero])
    (by rw [h.rd, h.wr, hs.rd, hs.wr, hp.rd]; exact ⟨⟨P, L⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ v₁ => ?_
  refine wp_lbu (a := St + BitVec.ofNat 64 i) (by decide)
    (by rw [v₁.other _ (by decide), h.t6, BitVec.add_zero])
    (by rw [v₁.rd, v₁.wr, h.rd, h.wr, hs.rd, hs.wr, hp.wr]
        exact ⟨⟨St, 16⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) fun t₂ v₂ => ?_
  refine wp_xor fun t₃ v₃ => ?_
  refine wp_sb (a := St + BitVec.ofNat 64 i) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), h.t6, BitVec.add_zero])
    (by rw [v₃.wr, v₂.wr, v₁.wr, h.wr, hs.wr, hp.wr]
        exact ⟨⟨St, 16⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) fun t₄ g₄ => ?_
  refine wp_addi (imm := 1) (by decide) fun t₅ v₅ => wp_addi (imm := 1) (by decide) fun t₆ v₆ =>
    wp_subi (imm := 1) (by decide) fun t₇ v₇ => WP.block_nil ?_
  have rP : t.mem (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact pS
  have rS : t.mem (St + BitVec.ofNat 64 i) = s.mem (St + BitVec.ofNat 64 i) := by
    rw [h.bytes i (by omega)]; simp
  have hv : (t₃.gpr .t3).setWidth 8 = s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (St + BitVec.ofNat 64 i) := by
    rw [v₃.gpr, v₂.other _ (by decide), v₂.gpr, v₁.gpr, v₁.mem, rP, rS, Bytes.xor_setWidth]
  have hm : t₇.mem = t.mem.writeW (St + BitVec.ofNat 64 i)
      (s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (St + BitVec.ofNat 64 i)) := by
    rw [v₇.mem, v₆.mem, v₅.mem, g₄.mem, hv, v₃.mem, v₂.mem, v₁.mem]
  refine ⟨by omega, ?_, ?_, ?_, fun r h1 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, fun j hj => ?_, ?_⟩
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, g₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h.t5, Offset.add_add]
  · rw [v₇.other _ (by decide), v₆.gpr, v₅.other _ (by decide), g₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h.t6, Offset.add_add]
  · rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), g₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h.t1, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [v₇.other _ h1, v₆.other _ h6, v₅.other _ h5, g₄.gpr, v₃.other _ h3, v₂.other _ h4, v₁.other _ h3,
      h.gpr r h1 h3 h4 h5 h6]
  · rw [v₇.rd, v₆.rd, v₅.rd, g₄.rd, v₃.rd, v₂.rd, v₁.rd, h.rd]
  · rw [v₇.wr, v₆.wr, v₅.wr, g₄.wr, v₃.wr, v₂.wr, v₁.wr, h.wr]
  · rw [v₇.sp, v₆.sp, v₅.sp, g₄.sp, v₃.sp, v₂.sp, v₁.sp, h.sp]
  · rw [hm, WriteBytes.writeW8_apply]
    by_cases e : j = i
    · subst e; simp
    · have hne : ¬ (St + BitVec.ofNat 64 j = St + BitVec.ofNat 64 i) := fun h' => e (by
        have := congrArg (fun a => (a - St).toNat) h'
        simp only [Mem.sub_ofNat_toNat St (show j < 2 ^ 64 by omega),
          Mem.sub_ofNat_toNat St (show i < 2 ^ 64 by omega)] at this
        exact this)
      simp only [hne, ite_false]
      rw [h.bytes j hj]
      by_cases hj' : j < i
      · simp [hj', show j < i + 1 by omega]
      · simp [hj', show ¬ j < i + 1 by omega]
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem xorLoop_wp (hL : L < 16) {s : State} (hs : FA s₀ W St P S L s) {i : Nat} (hi : i < L) {t : State}
    (h : XInv s St P L i t) : WP isa xorLoop t (XInv s St P L L) := by
  refine WP.loop (M := isa) (Q := XInv s St P L L)
    (fun (n : Nat) (u : State) => ∃ j, n = L - j ∧ j < L ∧ XInv s St P L j u) ?_ (L - i) t ⟨i, rfl, hi, h⟩
  rintro n u ⟨j, rfl, hj, hu⟩
  refine WP.mono (xorStep_wp hp hL hs hj hu) fun u' h' => ?_
  have ev := eval_nonzero_ofNat u' .t1 (k := L - (j + 1)) (by omega) h'.t1
  by_cases hz : L - (j + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    have e : j + 1 = L := by omega
    rw [e] at h'; exact h'
  · right
    exact ⟨by rw [ev]; simp [hz], L - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

theorem partial_wp (hL : L < 16) {s : State} (h : FA s₀ W St P S L s) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.st_wrap
  have kw := hp.key_wrap
  unfold partialBlock Impl.AesCbc.RISCV64.mov
  have A : WP isa (.block [.addi .t5 .a3 0, .addi .t6 .a2 0, .addi .t1 .a4 0]) s (XInv s St P L 0) := by
    refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
    refine ⟨by omega, ?_, ?_, ?_, fun r h1 _ _ h5 h6 => ?_, ?_, ?_, ?_,
      fun j hj => by rw [u₃.mem, u₂.mem, u₁.mem]; simp, ?_⟩
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.a3, BitVec.add_zero]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.a2, BitVec.add_zero]
    · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.a4, Nat.sub_zero]
    · rw [u₃.other _ h1, u₂.other _ h6, u₁.other _ h5]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
    · rw [u₃.sp, u₂.sp, u₁.sp]
    · rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _
  refine WP.seq (WP.mono A fun t₀ h₀ => ?_)
  refine WP.seq (WP.mono (Q := XInv s St P L L) ?_ fun t₁ h₁ => ?_)
  · have ev := eval_zero_ofNat t₀ .t1 (k := L - 0) (by omega) h₀.t1
    rw [Nat.sub_zero] at ev
    by_cases hz : L = 0
    · refine WP.ite true (by rw [ev, hz]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      rw [hz]; rw [hz] at h₀; exact h₀
    · exact WP.ite false (by rw [ev]; simp [hz]) (fun h => by cases h)
        fun _ => xorLoop_wp hp hL h (by omega) h₀
  -- `0x80` after the bytes, and `K2`.
  rw [padK2, List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_lbu (a := St + BitVec.ofNat 64 L) (by decide) (by rw [h₁.t6, BitVec.add_zero])
    (by rw [h₁.rd, h₁.wr, h.rd, h.wr, hp.wr]
        exact ⟨⟨St, 16⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) fun t₂ v₂ => ?_
  refine wp_xori (by decide) fun t₃ v₃ => ?_
  refine wp_sb (a := St + BitVec.ofNat 64 L) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), h₁.t6, BitVec.add_zero])
    (by rw [v₃.wr, v₂.wr, h₁.wr, h.wr, hp.wr]
        exact ⟨⟨St, 16⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) fun t₄ g₄ => ?_
  refine wp_addi (imm := 256) (by decide) fun t₅ v₅ => ?_
  have g₅ (r : Reg) (h1 : r ≠ .t1) (h3 : r ≠ .t3) (h4 : r ≠ .t4) (h5 : r ≠ .t5) (h6 : r ≠ .t6) :
      t₅.gpr r = s.gpr r := by
    rw [v₅.other _ h5, g₄.gpr, v₃.other _ h3, v₂.other _ h3, h₁.gpr r h1 h3 h4 h5 h6]
  have rd₅ : t₅.rd = s.rd := by rw [v₅.rd, g₄.rd, v₃.rd, v₂.rd, h₁.rd]
  have wr₅ : t₅.wr = s.wr := by rw [v₅.wr, g₄.wr, v₃.wr, v₂.wr, h₁.wr]
  refine xorInto_wp (P := St) (Q := W + BitVec.ofNat 64 256) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a2])
    (by rw [v₅.gpr, g₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide),
      h₁.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a0])
    (hp.rKey (by rw [rd₅, h.rd]) (by decide)) (hp.wSt (by rw [wr₅, h.wr]))
    (hp.key_st.symm.sub_right (FPre.key_sub (by decide))) fun t₆ g₆ x₆ f₆ rd₆ wr₆ sp₆ => WP.block_nil ?_
  have hb : (t₃.gpr .t3).setWidth 8 = s.mem (St + BitVec.ofNat 64 L) ^^^ 0x80 := by
    rw [v₃.gpr, v₂.gpr, h₁.bytes L (by omega)]; simp
  have hm₄ : t₄.mem = t₁.mem.writeW (St + BitVec.ofNat 64 L) (s.mem (St + BitVec.ofNat 64 L) ^^^ 0x80) := by
    rw [g₄.mem, hb, v₃.mem, v₂.mem]
  have hfm : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s.mem := by rw [h.mem]; exact FPre.fin_frame
  have f₅ : Frame [⟨St, 16⟩] s.mem t₅.mem := by
    rw [v₅.mem, hm₄]
    exact h₁.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have fr : Frame [⟨St, 16⟩] s.mem t₆.mem := f₅.trans f₆
  refine ⟨by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a0],
    by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a1],
    by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.a2],
    by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.s1],
    fun r hr h1 => ?_, by rw [rd₆, rd₅, h.rd], by rw [wr₆, wr₅, h.wr], by rw [sp₆, v₅.sp, g₄.sp, v₃.sp, v₂.sp, h₁.sp, h.sp],
    by rw [← h.mem]; exact fr, ?_⟩
  · obtain ⟨-, h1', -, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [g₆ r h3 h4, g₅ r h1' h3 h4 h5 h6, h.keep r hr h1]
  · -- Byte by byte.
    have k2 : bytesAt t₅.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s₀.mem (W + BitVec.ofNat 64 256) 16 :=
      hp.key_frame (hfm.trans (f₅.mono (by simp))) (by decide)
    rw [x₆, k2]
    refine Proof.Cmac.ext16 (by simp [Spec.Cbc.xor, Proof.Cmac.bytesAt_length])
      (by rw [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, length_mn _ _ _ (by omega)]; rfl) fun k hk => ?_
    rw [getD_xor_mn _ _ _ _ (by omega) hk, cbc_xor,
      Proof.Cmac.getD_xor (by simp [Proof.Cmac.bytesAt_length]) (by simp [Proof.Cmac.bytesAt_length]; exact hk),
      Proof.Cmac.getD_bytesAt _ _ hk, Proof.Cmac.getD_bytesAt _ _ hk, v₅.mem, hm₄, WriteBytes.writeW8_apply,
      h₁.bytes k hk]
    simp only [show L ≠ 16 by omega, ite_false]
    have cS : s.mem (St + BitVec.ofNat 64 k) = s₀.mem (St + BitVec.ofNat 64 k) := by
      have := congrArg (fun l => l.getD k 0) hp.st_fin
      simp only [Proof.Cmac.getD_bytesAt _ _ hk] at this
      rw [h.mem]; exact this
    have heq : (St + BitVec.ofNat 64 k = St + BitVec.ofNat 64 L) ↔ k = L := by
      constructor
      · intro e
        have := congrArg (fun a => (a - St).toNat) e
        simp only [Mem.sub_ofNat_toNat St (show k < 2 ^ 64 by omega),
          Mem.sub_ofNat_toNat St (show L < 2 ^ 64 by omega)] at this
        exact this
      · intro e; rw [e]
    rcases Nat.lt_trichotomy k L with hkL | hkL | hkL
    · have pS : s.mem (P + BitVec.ofNat 64 k) = s₀.mem (P + BitVec.ofNat 64 k) := by
        have := congrArg (fun l => l.getD k 0) (hp.last_frame hfm)
        simp only [Proof.Cmac.getD_bytesAt _ _ hkL] at this
        exact this
      simp only [show ¬ (St + BitVec.ofNat 64 k = St + BitVec.ofNat 64 L) by rw [heq]; omega, hkL, ite_false,
        ite_true, pS, cS]
      ac_rfl
    · subst hkL
      simp only [Nat.lt_irrefl, ite_false, ite_true, cS]
      ac_rfl
    · simp only [show ¬ (St + BitVec.ofNat 64 k = St + BitVec.ofNat 64 L) by rw [heq]; omega,
        show ¬ k < L by omega, show k ≠ L by omega, ite_false, cS]
      exact congrArg _ BitVec.xor_zero.symm

/-! ## Before and after the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : CallPre s W St S R
  s1 : s.gpr .s1 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St, 16⟩] (finMem s₀ S) s.mem
  st : bytesAt s.mem St 16 = Spec.Cmac.xor (bytesAt s₀.mem St 16) (mn s₀.mem W P L)

theorem args_wp {s : State} (h : BPost s₀ W St P S L s) :
    WP isa (.block [.li .a3 1, Impl.AesCbc.RISCV64.mov .a4 .s1]) s (FMid s₀ W St P S L R) := by
  have := hp.st_wrap
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_li (imm := 1) (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd, h.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hp.rounds, hp.key_st.sub_left (Region.sub_prefix (by decide)),
      (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
      hp.st_scr.sub_right (Region.sub_prefix (by decide)), hp.st_wrap, ?_, ?_⟩,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.s1], fun r hr h1 => ?_, rd₂, wr₂,
    by rw [u₂.sp, u₁.sp, h.sp], by rw [u₂.mem, u₁.mem]; exact h.frame, by rw [u₂.mem, u₁.mem]; exact h.st⟩
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.a0]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.a1, ← hp.a1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.a2]
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [u₂.gpr, u₁.other _ (by decide), h.s1]
  · rw [rd₂, wr₂, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W, 272⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₂, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h3, h4, -⟩ := preserved_ne r hr
    rw [u₂.other _ h4, u₁.other _ h3, h.keep r hr h1]

theorem finPre_wp : WP isa finPre s₀ (FMid s₀ W St P S L R) := by
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ ⟨h₁, ev₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀ W St P S L) ?_ fun _ h => args_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) h₁)

end

theorem finalize_wp {s₀ : State} (h0 : finalizeRISCV64.pre s₀) :
    WP isa finalize s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ finalizeRISCV64.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .a0 = W at hp
  generalize hSt : s₀.gpr .a2 = St at hp
  generalize hP : s₀.gpr .a3 = P at hp
  generalize hS : s₀.gpr .a5 = S at hp
  generalize hL : (s₀.gpr .a4).toNat = L at hp
  generalize hR : (s₀.gpr .a1).toNat = R at hp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
    encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  have slotD : ∀ p ∈ finSaved, ∀ r ∈ [(⟨St, 16⟩ : Region), ⟨S, 2048⟩],
      Region.Disjoint ⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    have hb := fin_bound p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_scr.symm.sub_left (svOf_sub S (by omega))
    · exact svOf_ws S (by omega)
  have hsv : Spill.Saved (svOf S) (finG s₀ S) finSaved s₂.mem :=
    ((Spill.saveMem_saved (by decide) s₀.mem (svOf S) _).frame h₁.frame fun p hp' r hr =>
      slotD p hp' r (by simp only [List.mem_singleton] at hr; subst hr; simp)).frame
      c.frame fun p hp' r hr => slotD p hp' r hr
  have s1₂ : s₂.gpr .s1 = S := by rw [c.saved _ (by decide), h₁.s1]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  rw [finRestore, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s1) fun s₃ e => ?_
  subst e
  rw [s1₂, show finSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 finSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := finSaved) (B := svOf S) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) hsv) fun s₄ r₄ => ?_
  · have := fin_bound p hp'
    have := pad_lt (S + BitVec.ofNat 64 2048)
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [rdwr₂, hp.rd, hp.wr]
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : finG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases h1 : r = .s1
    · left; subst h1; decide
    · right; rw [RegUpd.gpr_write_of_ne _ _ h0, c.saved r hr, h₁.keep r hr h1, g₀ r h0]
  · rw [r₄.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, c.sp, h₁.sp]
  · intro hk msg hm hne hst
    rw [hW, hR] at hk hst ⊢
    rw [hSt] at hst ⊢
    rw [hL] at hne
    rw [hP, hL]
    have hfm : Frame [⟨St, 16⟩, ⟨S, 2176⟩] s₀.mem s₁.mem :=
      FPre.fin_frame.trans (h₁.frame.mono (by simp))
    have sch : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      have := hp.key_frame hfm (d := 0) (n := 16 * (R + 1)) (by omega)
      rwa [BitVec.add_zero] at this
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [r₄.mem, RegUpd.mem_write, c.out, cipher_bytes, sch, h₁.st, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne)]

end VG.Proof.CmacAes.RISCV64
