module

public import VerifiedGarbage.Proof.CmacAes.RISCV64.Contract
import VerifiedGarbage.Proof.Cmac.RISCV64.Dbl
public import VerifiedGarbage.Impl.CmacAes.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.AesCbc.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Cmac

/-!
# AES-CMAC on RISC-V: `vg_cmac_aes_subkeys`

As on PPC64LE (`Proof/CmacAes/PPC64LE/Subkeys.lean`): the return address and
`s1`, `s2` saved in the scratch buffer at `svOf S` (`Spill.save_ok`), the
first block of `subkeys` zeroed (`Bytes.storeBytes_ok`) and enciphered in
place (`blk_call`), doubled there and into the second block (`dbl_wp`), and
the registers restored (`Spill.restore_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.CmacAes.RISCV64
open VG.Proof.AesCbc.RISCV64 (CallPre CallPost blk_call in_rw savePtr_ok encryptBlocks_noFrames)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.RISCV64 (dbl_wp wp_xori dbl_spec16)

/-- Where the registers are saved, from the scratch buffer `S`: `S + 2048`
rounded up to a multiple of 8. -/
abbrev svOf (S : Addr) : Addr := S + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (S + BitVec.ofNat 64 2048))

theorem svOf_add (S : Addr) (d : Nat) :
    svOf S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 (2048 + pad (S + BitVec.ofNat 64 2048) + d) :=
  align_add _ _ _

/-- A slot at `svOf S + d`, within the scratch buffer. -/
theorem svOf_sub (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    Region.Sub ⟨svOf S + BitVec.ofNat 64 d, n⟩ ⟨S, 2176⟩ := by
  have := pad_lt (S + BitVec.ofNat 64 2048)
  rw [svOf_add]; exact Offset.sub_base _ (by omega)

/-- A slot at `svOf S + d`, above the working space of the block function. -/
theorem svOf_ws (S : Addr) {d n : Nat} (h : d + n ≤ 121) :
    Region.Disjoint ⟨svOf S + BitVec.ofNat 64 d, n⟩ ⟨S, 2048⟩ := by
  have := pad_lt (S + BitVec.ofNat 64 2048)
  rw [svOf_add]; exact Offset.disjoint_base _ (by omega) (by omega)

/-- The precondition, by name: the schedule `W`, the subkeys `K`, the scratch
buffer `S` and the rounds `R`. -/
structure SPre (s₀ : State) (W K S : Addr) (R : Nat) : Prop where
  a0 : s₀.gpr .a0 = W
  a2 : s₀.gpr .a2 = K
  a3 : s₀.gpr .a3 = S
  a1 : (s₀.gpr .a1).toNat = R
  rd : s₀.rd = [⟨W, 240⟩]
  wr : s₀.wr = [⟨K, 32⟩, ⟨S, 2176⟩]
  sch_k : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  sch_scr : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  k_scr : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  k_wrap : K.toNat + 32 ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem SPre.of {s₀ : State} (h : subkeysRISCV64.pre s₀) :
    SPre s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h⟩

theorem sk_bound : ∀ p ∈ skSaved, 16 ≤ p.2 ∧ p.2 + 8 ≤ 40 := by decide

/-- The values saved: `t0` holds `svOf S`. -/
abbrev skG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (svOf S)).gpr

/-- The slots, from `svOf S`. -/
abbrev skSlots (S : Addr) : Region := ⟨svOf S + BitVec.ofNat 64 16, 24⟩

/-- What `subkeysPre` leaves. -/
structure SkMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : CallPre s W K S R
  s1 : s.gpr .s1 = K
  s2 : s.gpr .s2 = S
  keep : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → s.gpr r = s₀.gpr r
  saved : Spill.Saved (svOf S) (skG s₀ S) skSaved s.mem
  zero : bytesAt s.mem K 16 = Spec.Cmac.zeros 16
  frame : Frame [⟨K, 16⟩, skSlots S] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .t5 ∧ r ≠ .t6 ∧ r ≠ .ra ∧ r ≠ .a0 ∧
      r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 := by
  revert hr; cases r <;> decide

theorem subkeysPre_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (SkMid s₀ W K S R) := by
  have hRr := hp.rounds
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inK (d : Nat) (h : d + 1 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 1 := by
    rw [hp.wr]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  rw [subkeysPre, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a3) fun s₁ e => ?_
  subst e
  rw [hp.a3, show skSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 skSaved from rfl]
  have t₀ : (s₀.write .t0 (svOf S)).gpr .t0 = svOf S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (svOf S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := skSaved) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := sk_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    have := pad_lt (S + BitVec.ofNat 64 2048)
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  generalize ht : ({ (s₀.write .t0 (svOf S)) with
    mem := Spill.saveMem (s₀.write .t0 (svOf S)).mem ((s₀.write .t0 (svOf S)).gpr .t0)
      (s₀.write .t0 (svOf S)).gpr skSaved } : State) = t
  have memt : t.mem = Spill.saveMem s₀.mem (svOf S) (skG s₀ S) skSaved := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀]; rfl
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  have spt : t.sp = s₀.sp := by rw [← ht]; rfl
  simp only [List.cons_append, List.nil_append]
  unfold Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => ?_
  have k₃ : s₃.gpr .s1 = K := by rw [u₃.other _ (by decide), u₂.gpr, gt _ (by decide), hp.a2]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.storeBytes_ok (tmp := .t1) (dst := .s1) (doff := 0) (bs := List.replicate 16 0)
    (by decide) (by decide) (by decide) (fun i hi => ?_)) fun s₄ h₄ => ?_
  · rw [u₃.wr, u₂.wr, wrt, k₃, Nat.zero_add]; exact inK i (by simp at hi; omega)
  refine wp_mv fun s₅ u₅ => wp_li (by decide) fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, h₄.rd, u₃.rd, u₂.rd, rdt]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, h₄.wr, u₃.wr, u₂.wr, wrt]
  have mem₇ : s₇.mem = s₄.mem := by rw [u₇.mem, u₆.mem, u₅.mem]
  have k₄ : s₄.gpr .s1 = K := by rw [h₄.gpr _ (by decide), k₃]
  have s2₄ : s₄.gpr .s2 = S := by
    rw [h₄.gpr _ (by decide), u₃.gpr, u₂.other _ (by decide), gt _ (by decide), hp.a3]
  -- The memory.
  have f₃ : Frame [⟨K, 16⟩] s₃.mem s₄.mem := by
    have := h₄.frame; rwa [k₃, BitVec.add_zero, List.length_replicate] at this
  have m₃ : s₃.mem = Spill.saveMem s₀.mem (svOf S) (skG s₀ S) skSaved := by rw [u₃.mem, u₂.mem, memt]
  have slotK : ∀ p ∈ skSaved, ∀ r ∈ [(⟨K, 16⟩ : Region)], Region.Disjoint ⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    simp only [List.mem_singleton] at hr; subst hr
    have := sk_bound p hp'
    exact (hp.k_scr.symm.sub_left (svOf_sub S (by omega))).sub_right (Region.sub_prefix (by decide))
  refine ⟨CallPre.mk ?_ ?_ ?_ ?_ ?_ hRr (hp.sch_k.sub_right (Region.sub_prefix (by decide)))
      (hp.sch_scr.sub_right (Region.sub_prefix (by decide)))
      ((hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))
      (by omega) ?_ ?_, ?_, ?_, fun r hr h1 h2 => ?_, ?_, ?_, ?_, rd₇, wr₇, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), h₄.gpr _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), hp.a0]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), h₄.gpr _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), gt _ (by decide), ← hp.a1, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, k₄]
  · rw [u₇.other _ (by decide), u₆.gpr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), s2₄]
  · rw [rd₇, wr₇, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W, 240⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₇, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), k₄]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), s2₄]
  · obtain ⟨h0, h1', -, -, -, -, -, -, -, -, h₂, h₃, h₄', -⟩ := preserved_ne r hr
    rw [u₇.other _ h₄', u₆.other _ h₃, u₅.other _ h₂, h₄.gpr _ h1', u₃.other _ h2, u₂.other _ h1, gt _ h0]
  · have sv₃ : Spill.Saved (svOf S) (skG s₀ S) skSaved s₃.mem := by
      rw [m₃]; exact Spill.saveMem_saved (by decide) s₀.mem (svOf S) _
    rw [mem₇]; exact sv₃.frame f₃ slotK
  · rw [mem₇]
    apply List.ext_getElem (by simp [bytesAt, Spec.Cmac.zeros])
    intro j h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, Spec.Cmac.zeros, List.getElem_replicate]
    have := h₄.stored j (by simpa using h₁)
    rw [k₃, Nat.zero_add] at this
    have hz : ∀ j < 16, (List.replicate 16 (0 : Nat)).getD j 0 = 0 := by decide
    rw [this, hz j h₁]; rfl
  · have fa : Frame [⟨K, 16⟩, skSlots S] s₀.mem s₃.mem := by
      rw [m₃]
      exact (Spill.saveMem_frame (lo := 16) (n := 24) sk_bound (by omega) s₀.mem (svOf S) _).mono (by simp)
    rw [mem₇]; exact fa.trans (f₃.mono (by simp))
  · rw [u₇.sp, u₆.sp, u₅.sp, h₄.sp, u₃.sp, u₂.sp, spt]

/-- `CIPH_K` of a block as `vg_aes_encrypt_blocks` computes it. -/
theorem cipher_bytes (R : Nat) (w : List Byte) (m : Mem) (p : Addr) :
    (Spec.Aes.cipher R w (Spec.Aes.stateAt m p)).toList = Spec.Cmac.aesWith R w (bytesAt m p 16) :=
  (Proof.AesCbc.aesWith_state R w m p).symm

theorem subkeys_wp {s₀ : State} (h0 : subkeysRISCV64.pre s₀) :
    WP isa subkeys s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ subkeysRISCV64.post s₀ s' := by
  have hp := SPre.of h0
  generalize hW : s₀.gpr .a0 = W at hp
  generalize hK : s₀.gpr .a2 = K at hp
  generalize hS : s₀.gpr .a3 = S at hp
  generalize hR : (s₀.gpr .a1).toNat = R at hp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inK (d : Nat) (h : d + 1 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 1 := by
    rw [hp.wr]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega))
  have rIn (a : Addr) (h : InRegions s₀.wr a 1) : InRegions (s₀.rd ++ s₀.wr) a 1 := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (subkeysPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
    encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s₁.gpr r := c.saved r hr
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  have wr₂ : s₂.wr = s₀.wr := by rw [c.wr, h₁.wr]
  rw [subkeysPost, List.append_assoc, List.append_assoc]
  refine dbl_wp (K := K) (src := 0) (dst := 0) (by decide) (by decide) dbl_spec16
    (by rw [g₂ _ (by decide), h₁.s1]) (.inl rfl) (by decide)
    (by decide) (by omega) (fun j hj => by rw [rdwr₂, Nat.zero_add]; exact rIn _ (inK j (by omega)))
    (fun j hj => by rw [wr₂, Nat.zero_add]; exact inK j (by omega)) fun s₃ g₃ rd₃ wr₃ sp₃ f₃ b₃ => ?_
  refine dbl_wp (K := K) (src := 0) (dst := 16) (by decide) (by decide) dbl_spec16
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), h₁.s1]) (.inr (by decide))
    (by decide) (by decide) (by omega)
    (fun j hj => by rw [rd₃, wr₃, rdwr₂, Nat.zero_add]; exact rIn _ (inK j (by omega)))
    (fun j hj => by rw [wr₃, wr₂]; exact inK (16 + j) (by omega)) fun s₄ g₄ rd₄ wr₄ sp₄ f₄ b₄ => ?_
  -- The registers restored.
  have s2₄ : s₄.gpr .s2 = S := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide), h₁.s2]
  rw [WP.block_append_iff]
  refine WP.mono (savePtr_ok .s2) fun s₅ e => ?_
  subst e
  rw [s2₄]
  -- The slots, kept by the call and the doublings.
  have slotS (p : Reg × Nat) (hp' : p ∈ skSaved) : Region.Sub ⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2176⟩ := by
    have := sk_bound p hp'; exact svOf_sub S (by omega)
  have slotK (p : Reg × Nat) (hp' : p ∈ skSaved) (e : Nat) (he : e ≤ 16) :
      (⟨svOf S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint ⟨K + BitVec.ofNat 64 e, 16⟩ :=
    (hp.k_scr.symm.sub_left (slotS p hp')).sub_right (Offset.sub_base _ (by omega))
  have sv₂ := h₁.saved.frame c.frame fun p hp' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := slotK p hp' 0 (by decide); rwa [BitVec.add_zero] at this
    · exact svOf_ws S (by have := sk_bound p hp'; omega)
  have sv₄ : Spill.Saved (svOf S) (skG s₀ S) skSaved s₄.mem :=
    (sv₂.frame f₃ fun p hp' r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact slotK p hp' 0 (by decide)).frame f₄
      fun p hp' r hr => by simp only [List.mem_singleton] at hr; subst hr; exact slotK p hp' 16 (by decide)
  rw [show skSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 skSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := skSaved) (B := svOf S) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₄) fun s₆ r₆ => ?_
  · show InRegions (s₄.rd ++ s₄.wr) _ 8
    rw [rd₄, wr₄, rd₃, wr₃, rdwr₂, hp.rd, hp.wr]
    have := pad_lt (S + BitVec.ofNat 64 2048)
    have := sk_bound p hp'
    exact ⟨⟨S, 2176⟩, by simp, by rw [svOf_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : skG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · obtain ⟨h0', h1', h2', h3', h4', -, -, -, -, -, -, -, -, -⟩ := preserved_ne r hr
    rw [r₆.gpr_of (r := r) ?_, g₀ r h0']
    by_cases hv : r = .s1 ∨ r = .s2
    · left; rcases hv with rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0', g₄ r h1' h2' h3' h4', g₃ r h1' h2' h3' h4', g₂ r hr,
        h₁.keep r hr (fun e => hv (.inl e)) (fun e => hv (.inr e)), g₀ r h0']
  · rw [r₆.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · rw [r₆.sp, RegUpd.sp_write, sp₄, sp₃, c.sp, h₁.sp]
  · show bytesAt s₆.mem (s₀.gpr .a2) 32 = _
    have schB : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      refine Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.sch_k.sub_left (Region.sub_prefix hRb)).sub_right (Region.sub_prefix (by decide))
      · exact (hp.sch_scr.sub_left (Region.sub_prefix hRb)).sub_right (svOf_sub S (by decide))
    have L : bytesAt s₂.mem K 16 = ciphAt s₀.mem W R (Spec.Cmac.zeros 16) := by
      rw [c.out, cipher_bytes, schB, h₁.zero]
    have b3 : bytesAt s₃.mem K 16 = Spec.Cmac.dbl 16 (bytesAt s₂.mem K 16) := by
      rw [BitVec.add_zero] at b₃; exact b₃
    have b4lo : bytesAt s₄.mem K 16 = bytesAt s₃.mem K 16 :=
      Proof.Cmac.bytesAt_frame16 f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base K (by decide) (by omega)).symm
    have b4hi : bytesAt s₄.mem (K + BitVec.ofNat 64 16) 16 = Spec.Cmac.dbl 16 (bytesAt s₃.mem K 16) := by
      rw [BitVec.add_zero] at b₄; exact b₄
    rw [r₆.mem, RegUpd.mem_write, hK, Proof.Cmac.bytesAt_32, b4lo, b4hi, b3, L, hW, hR]
    rfl

end VG.Proof.CmacAes.RISCV64
