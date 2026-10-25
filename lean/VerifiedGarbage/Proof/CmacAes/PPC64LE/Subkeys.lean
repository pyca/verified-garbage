module

public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Contract
public import VerifiedGarbage.Proof.Cmac.Dbl64
public import VerifiedGarbage.Proof.Cmac.Block
public import VerifiedGarbage.Impl.CmacAes.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-CMAC on PPC64LE: `vg_cmac_aes_subkeys`

The return address and `r14`, `r15` saved in the scratch buffer
(`Spill.save_ok`), the first block of `subkeys` zeroed and enciphered in
place (`blk_call`), doubled there and into the second block (`dbl_wp`,
whose memory is `dblMem`: `Proof.Cmac.dbl_byteRev`), and the registers
restored (`Spill.restore_ok`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Proof.AesCbc.PPC64LE (CallPre CallPost blk_call in_rw)
open VG.Proof.Cmac (dblHi dblLo)
open VG.Spec.Aes (bytesAt)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `ldbrx t, a, b`. -/
theorem wp_ldbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 8)
    (k : ∀ s', Upd s s' t (byteRev64 (s.mem.readW ea 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := s.write t (byteRev64 (s.mem.readW ea 64))) ?_ (k _ (Upd.write _ _ _))
  rw [exec_loadRev_d hn (by rw [hea]; exact hin), hea]
  rfl

/-- `stdbrx t, a, b`. -/
theorem wp_stdbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (byteRev64 (s.gpr t))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW ea (byteRev64 (s.gpr t)) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [hea]; exact hout), hea]
  rfl

/-- `or d, n, m`. -/
theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

/-! ## Doubling a block -/

/-- The memory after `dbl src dst`, from `r14 = K`. -/
def dblMem (m : Mem) (K : Addr) (src dst : Nat) : Mem :=
  let hi := byteRev64 (m.readW (K + BitVec.ofNat 64 src) 64)
  let lo := byteRev64 (m.readW (K + BitVec.ofNat 64 (src + 8)) 64)
  (m.writeW (K + BitVec.ofNat 64 dst) (byteRev64 (dblHi hi lo))).writeW (K + BitVec.ofNat 64 (dst + 8))
    (byteRev64 (dblLo hi lo))

theorem dbl_wp {s : State} {K : Addr} {rest : List Instr} {Φ : State → Prop} (hk : s.gpr .r14 = K)
    {src dst : Nat} (hs : src + 8 < 2 ^ 15) (hd : dst + 8 < 2 ^ 15)
    (r₀ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 src) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 (src + 8)) 8)
    (w₀ : InRegions s.wr (K + BitVec.ofNat 64 dst) 8) (w₁ : InRegions s.wr (K + BitVec.ofNat 64 (dst + 8)) 8)
    (k : ∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s'.gpr r = s.gpr r) →
      s'.mem = dblMem s.mem K src dst → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block rest) s' Φ) :
    WP isa (.block (dbl src dst ++ rest)) s Φ := by
  simp only [dbl, List.cons_append, List.nil_append]
  refine wp_li (by omega_arith) fun s₁ u₁ => ?_
  refine wp_ldbrx (ea := K + BitVec.ofNat 64 src) (by decide) (by rw [u₁.other _ (by decide), u₁.gpr, hk])
    (by rw [u₁.rd, u₁.wr]; exact r₀) fun s₂ u₂ => ?_
  refine wp_li (by omega_arith) fun s₃ u₃ => ?_
  refine wp_ldbrx (ea := K + BitVec.ofNat 64 (src + 8)) (by decide)
    (by rw [u₃.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact r₁) fun s₄ u₄ => ?_
  refine wp_lsr (by decide) fun s₅ u₅ => wp_li (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ => ?_
  refine wp_li (by decide) fun s₈ u₈ => wp_and fun s₉ u₉ => ?_
  refine wp_lsr (by decide) fun s₁₀ u₁₀ => wp_lsl (by decide) fun s₁₁ u₁₁ => wp_or fun s₁₂ u₁₂ => ?_
  refine wp_lsl (by decide) fun s₁₃ u₁₃ => wp_xor fun s₁₄ u₁₄ => ?_
  have m₁₄ : s₁₄.mem = s.mem := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem]
  have k₁₄ : s₁₄.gpr .r14 = K := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk]
  have h9 : s₄.gpr .r9 = byteRev64 (s.mem.readW (K + BitVec.ofNat 64 src) 64) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
  have h10 : s₄.gpr .r10 = byteRev64 (s.mem.readW (K + BitVec.ofNat 64 (src + 8)) 64) := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  have m11 : s₉.gpr .r11 = (BitVec.ofNat 64 0 - s₄.gpr .r9 >>> 63) &&& BitVec.ofNat 64 0x87 := by
    rw [u₉.gpr, u₈.other .r11 (by decide), u₈.gpr, u₇.gpr, u₆.gpr, u₆.other .r11 (by decide), u₅.gpr]
  have hi : s₁₄.gpr .r9 = dblHi (s₄.gpr .r9) (s₄.gpr .r10) := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, u₁₁.other .r12 (by decide),
      u₁₀.gpr, u₁₀.other .r9 (by decide), u₉.other .r9 (by decide), u₉.other .r10 (by decide),
      u₈.other .r9 (by decide), u₈.other .r10 (by decide), u₇.other .r9 (by decide), u₇.other .r10 (by decide),
      u₆.other .r9 (by decide), u₆.other .r10 (by decide), u₅.other .r9 (by decide), u₅.other .r10 (by decide)]
    rfl
  have lo : s₁₄.gpr .r10 = dblLo (s₄.gpr .r9) (s₄.gpr .r10) := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₃.other .r11 (by decide), u₁₂.other .r10 (by decide), u₁₂.other .r11 (by decide),
      u₁₁.other .r10 (by decide), u₁₁.other .r11 (by decide), u₁₀.other .r10 (by decide),
      u₁₀.other .r11 (by decide), m11, u₉.other .r10 (by decide), u₈.other .r10 (by decide),
      u₇.other .r10 (by decide), u₆.other .r10 (by decide), u₅.other .r10 (by decide)]
    rfl
  have wr₁₄ : s₁₄.wr = s.wr := by
    rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₁₄ : s₁₄.rd = s.rd := by
    rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine wp_li (by omega_arith) fun s₁₅ u₁₅ => ?_
  refine wp_stdbrx (ea := K + BitVec.ofNat 64 dst) (by decide) (by rw [u₁₅.other _ (by decide), u₁₅.gpr, k₁₄])
    (by rw [u₁₅.wr, wr₁₄]; exact w₀) fun s₁₆ u₁₆ => ?_
  refine wp_li (by omega_arith) fun s₁₇ u₁₇ => ?_
  refine wp_stdbrx (ea := K + BitVec.ofNat 64 (dst + 8)) (by decide)
    (by rw [u₁₇.other _ (by decide), u₁₇.gpr, u₁₆.gpr, u₁₅.other _ (by decide), k₁₄])
    (by rw [u₁₇.wr, u₁₆.wr, u₁₅.wr, wr₁₄]; exact w₁) fun s₁₈ u₁₈ => ?_
  refine k s₁₈ (fun r h9' h10' h11' h12' => ?_) ?_ ?_ ?_
  · rw [u₁₈.gpr, u₁₇.other _ h11', u₁₆.gpr, u₁₅.other _ h11', u₁₄.other _ h10', u₁₃.other _ h10',
      u₁₂.other _ h9', u₁₁.other _ h9', u₁₀.other _ h12', u₉.other _ h11', u₈.other _ h12', u₇.other _ h11',
      u₆.other _ h12', u₅.other _ h11', u₄.other _ h10', u₃.other _ h11', u₂.other _ h9', u₁.other _ h11']
  · rw [u₁₈.mem, u₁₇.mem, u₁₇.other .r10 (by decide), u₁₆.gpr, u₁₆.mem, u₁₅.mem, u₁₅.other .r10 (by decide),
      u₁₅.other .r9 (by decide), hi, lo, m₁₄, h9, h10]
    rfl
  · rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, rd₁₄]
  · rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, wr₁₄]

theorem dblMem_frame (m : Mem) (K : Addr) (src dst : Nat) :
    Frame [⟨K + BitVec.ofNat 64 dst, 16⟩] m (dblMem m K src dst) := by
  rw [dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
    (Offset.add_add _ _ _).symm]
  exact Proof.Cmac.frame_store2 _ _ _

theorem dblMem_bytes (m : Mem) (K : Addr) (src dst : Nat) :
    bytesAt (dblMem m K src dst) (K + BitVec.ofNat 64 dst) 16 =
      Spec.Cmac.dbl 16 (bytesAt m (K + BitVec.ofNat 64 src) 16) := by
  rw [dblMem, show K + BitVec.ofNat 64 (dst + 8) = K + BitVec.ofNat 64 dst + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    show K + BitVec.ofNat 64 (src + 8) = K + BitVec.ofNat 64 src + BitVec.ofNat 64 8 from
      (Offset.add_add _ _ _).symm,
    Proof.Cmac.bytesAt_store2, ← Proof.Cmac.dbl_byteRev, BitVec.add_zero]

/-! ## The whole function -/

/-- The precondition, by name: the schedule `W`, the subkeys `K`, the scratch
buffer `S` and the rounds `R`. -/
structure SPre (s₀ : State) (W K S : Addr) (R : Nat) : Prop where
  r3 : s₀.gpr .r3 = W
  r5 : s₀.gpr .r5 = K
  r6 : s₀.gpr .r6 = S
  r4 : (s₀.gpr .r4).toNat = R
  rd : s₀.rd = [⟨W, 240⟩]
  wr : s₀.wr = [⟨K, 32⟩, ⟨S, 2176⟩]
  sch_k : (⟨W, 240⟩ : Region).Disjoint ⟨K, 32⟩
  sch_scr : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2176⟩
  k_scr : (⟨K, 32⟩ : Region).Disjoint ⟨S, 2176⟩
  k_wrap : K.toNat + 32 ≤ 2 ^ 64
  scr_wrap : S.toNat + 2176 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem SPre.of {s₀ : State} (h : subkeysPPC64LE.pre s₀) :
    SPre s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r4).toNat :=
  let ⟨a, b, c, d, e, f, g, h⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h⟩

theorem bytesAt_32 (m : Mem) (p : Addr) :
    bytesAt m p 32 = bytesAt m p 16 ++ bytesAt m (p + BitVec.ofNat 64 16) 16 := by
  simp only [bytesAt]
  rw [show (32 : Nat) = 16 + 16 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

theorem sk_bound : ∀ p ∈ skSaved, 2064 ≤ p.2 ∧ p.2 + 8 ≤ 2088 := by decide

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) :
    r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧
      r ≠ .r11 ∧ r ≠ .r12 := by
  revert hr; cases r <;> decide

/-- `CIPH_K` of a block as `vg_aes_encrypt_blocks` computes it. -/
theorem cipher_bytes (R : Nat) (w : List Byte) (m : Mem) (p : Addr) :
    (Spec.Aes.cipher R w (Spec.Aes.stateAt m p)).toList = Spec.Cmac.aesWith R w (bytesAt m p 16) :=
  (Proof.AesCbc.aesWith_state R w m p).symm

/-- The memory before the call: the slots saved, and the first block of the
subkeys zeroed. -/
abbrev preMem (s₀ : State) (K S : Addr) : Mem :=
  Proof.Cmac.zero2 (Spill.saveMem s₀.mem S (s₀.write .r0 s₀.lr).gpr skSaved) K

/-- What `subkeysPre` leaves. -/
structure SkMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : CallPre s W K S R
  r14 : s.gpr .r14 = K
  r15 : s.gpr .r15 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → r ≠ .r15 → s.gpr r = s₀.gpr r
  mem : s.mem = preMem s₀ K S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem subkeysPre_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (SkMid s₀ W K S R) := by
  have hRr := hp.rounds
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega_arith))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega_arith))
  rw [subkeysPre, show skSaved.map (fun (r, d) => Instr.store .d r .r6 d) = Spill.saveCode .r6 skSaved from rfl]
  refine WP.cons exec_mflr (Spill.save_ok (b := .r6) (l := skSaved) (by decide) (by decide) (fun p hp' => ?_) ?_)
  · have := sk_bound p hp'
    show InRegions s₀.wr (s₀.gpr .r6 + BitVec.ofNat 64 p.2) 8
    rw [hp.r6]; exact inS _ (by omega_arith)
  generalize ht : ({ (s₀.write .r0 s₀.lr) with
    mem := (Spill.saveMem (s₀.write .r0 s₀.lr).mem ((s₀.write .r0 s₀.lr).gpr .r6) (s₀.write .r0 s₀.lr).gpr
      skSaved) } : State) = t
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, hr]
  have gt (r : Reg) (hr : r ≠ .r0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  have memt : t.mem = Spill.saveMem s₀.mem S (s₀.write .r0 s₀.lr).gpr skSaved := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [g₀ .r6 (by decide), hp.r6]; rfl
  have rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  have wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => ?_
  have k₃ : s₃.gpr .r5 = K := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gt _ (by decide), hp.r5]
  refine wp_std (a := K) (by decide) (by decide) (by rw [k₃]; simp)
    (by rw [u₃.wr, u₂.wr, u₁.wr, wrt]; simpa using inK 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_std (a := K + BitVec.ofNat 64 8) (by decide) (by decide) (by rw [u₄.gpr, k₃])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]; exact inK 8 (by decide)) fun s₅ u₅ => ?_
  refine wp_mr fun s₆ u₆ => wp_li (by decide) fun s₇ u₇ => wp_mr fun s₈ u₈ => wp_nil ?_
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, rdt]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, wrt]
  refine ⟨CallPre.mk ?_ ?_ ?_ ?_ ?_ hRr (hp.sch_k.sub_right (Region.sub_prefix (by decide)))
      (hp.sch_scr.sub_right (Region.sub_prefix (by decide)))
      ((hp.k_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))
      (by omega_arith) ?_ ?_, ?_, ?_, fun r hr h14 h15 => ?_, ?_, rd₈, wr₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gt _ (by decide), hp.r3]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gt _ (by decide), ← hp.r4,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, gt _ (by decide), hp.r5]
  · rw [u₈.other _ (by decide), u₇.gpr]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), gt _ (by decide), hp.r6]
  · rw [rd₈, wr₈, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W, 240⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₈, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨K, 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, gt _ (by decide), hp.r5]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), gt _ (by decide), hp.r6]
  · obtain ⟨h0', -, -, h5, h6, h7, -, h9, -⟩ := preserved_ne r hr
    rw [u₈.other _ h7, u₇.other _ h6, u₆.other _ h5, u₅.gpr, u₄.gpr, u₃.other _ h9, u₂.other _ h15,
      u₁.other _ h14, gt _ h0']
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, memt]; rfl

theorem subkeys_wp {s₀ : State} (h0 : subkeysPPC64LE.pre s₀) :
    WP isa subkeys s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      subkeysPPC64LE.post s₀ s' := by
  have hp := SPre.of h0
  generalize hW : s₀.gpr .r3 = W at hp
  generalize hK : s₀.gpr .r5 = K at hp
  generalize hS : s₀.gpr .r6 = S at hp
  generalize hR : (s₀.gpr .r4).toNat = R at hp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  have kw := hp.k_wrap
  have sw := hp.scr_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega_arith))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (K + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega_arith))
  have rIn (a : Addr) (h : InRegions s₀.wr a 8) : InRegions (s₀.rd ++ s₀.wr) a 8 := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (subkeysPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
    AesCbc.PPC64LE.encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  have g₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s₁.gpr r := c.saved r hr
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  have wr₂ : s₂.wr = s₀.wr := by rw [c.wr, h₁.wr]
  rw [subkeysPost, List.append_assoc, List.append_assoc]
  refine dbl_wp (K := K) (src := 0) (dst := 0) (by rw [g₂ _ (by decide), h₁.r14]) (by decide) (by decide)
    (by rw [rdwr₂]; exact rIn _ (inK 0 (by decide))) (by rw [rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₂]; exact inK 0 (by decide)) (by rw [wr₂]; exact inK 8 (by decide)) fun s₃ g₃ mem₃ rd₃ wr₃ => ?_
  refine dbl_wp (K := K) (src := 0) (dst := 16)
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide), h₁.r14]) (by decide)
    (by decide) (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 0 (by decide)))
    (by rw [rd₃, wr₃, rdwr₂]; exact rIn _ (inK 8 (by decide)))
    (by rw [wr₃, wr₂]; exact inK 16 (by decide)) (by rw [wr₃, wr₂]; exact inK 24 (by decide))
    fun s₄ g₄ mem₄ rd₄ wr₄ => ?_
  -- The memory.
  have slotS (p : Reg × Nat) (hp' : p ∈ skSaved) : Region.Sub ⟨S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2176⟩ :=
    Offset.sub_base _ (by have := sk_bound p hp'; omega_arith)
  have slotK (p : Reg × Nat) (hp' : p ∈ skSaved) (e : Nat) (he : e ≤ 16) :
      (⟨S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint ⟨K + BitVec.ofNat 64 e, 16⟩ :=
    (hp.k_scr.symm.sub_left (slotS p hp')).sub_right (Offset.sub_base _ (by omega_arith))
  have slotK0 (p : Reg × Nat) (hp' : p ∈ skSaved) : (⟨S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint ⟨K, 16⟩ := by
    have := slotK p hp' 0 (by decide); rwa [BitVec.add_zero] at this
  have sv₁ : Spill.Saved S (s₀.write .r0 s₀.lr).gpr skSaved s₁.mem := by
    rw [h₁.mem]
    exact (Spill.saveMem_saved (by decide) s₀.mem S _).frame (Proof.Cmac.frame_store2 K _ _) fun p hp' r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotK0 p hp'
  have sv₂ := sv₁.frame c.frame fun p hp' r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slotK0 p hp'
    · exact Offset.disjoint_base _ (by have := sk_bound p hp'; omega_arith) (by have := sk_bound p hp'; omega_arith)
  have sv₃ : Spill.Saved S (s₀.write .r0 s₀.lr).gpr skSaved s₃.mem := by
    rw [mem₃]; exact sv₂.frame (dblMem_frame _ _ _ _) fun p hp' r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotK p hp' 0 (by decide)
  have sv₄ : Spill.Saved S (s₀.write .r0 s₀.lr).gpr skSaved s₄.mem := by
    rw [mem₄]; exact sv₃.frame (dblMem_frame _ _ _ _) fun p hp' r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotK p hp' 16 (by decide)
  -- The registers and the return address restored.
  have r15₄ : s₄.gpr .r15 = S := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide), h₁.r15]
  rw [show skSaved.map (fun (r, d) => Instr.load .d r .r15 d) = Spill.restoreCode .r15 skSaved from rfl]
  refine Spill.restore_ok (b := .r15) (l := skSaved) (by decide) r15₄ (by decide) (by decide)
    (fun p hp' => ?_) sv₄ fun s₅ r₅ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := sk_bound p hp'
    rw [rd₄, wr₄, rd₃, wr₃, rdwr₂]; exact rIn _ (inS _ (by omega_arith))
  · show s₅.gpr r = _
    have h0 : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, (preserved_ne r hr).1]
    rw [r₅.gpr_of (r := r) ?_, h0]
    by_cases hv : r = .r14 ∨ r = .r15
    · left; rcases hv with rfl | rfl <;> decide
    · right
      obtain ⟨-, -, -, -, -, -, -, h9, h10, h11, h12⟩ := preserved_ne r hr
      rw [g₄ r h9 h10 h11 h12, g₃ r h9 h10 h11 h12, g₂ r hr, h₁.keep r hr (fun e => hv (.inl e))
        (fun e => hv (.inr e)), h0]
  · show s₅.gpr .r0 = _
    rw [r₅.gpr (.r0, 2080) (by decide)]; simp [State.write]
  · show bytesAt s₅.mem (s₀.gpr .r5) 32 = _
    have schB : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      rw [h₁.mem]
      refine (Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 K _ _) (fun r hr => ?_) (by omega_arith)).trans
        (Proof.Cmac.bytesAt_frame (Spill.saveMem_frame (lo := 2064) (n := 24) (fun p hp' => sk_bound p hp')
          (by omega_arith) s₀.mem S _) (fun r hr => ?_) (by omega_arith))
      · simp only [List.mem_singleton] at hr; subst hr
        exact (hp.sch_k.sub_left (Region.sub_prefix hRb)).sub_right (Region.sub_prefix (by decide))
      · simp only [List.mem_singleton] at hr; subst hr
        exact (hp.sch_scr.sub_left (Region.sub_prefix hRb)).sub_right (Offset.sub_base _ (by decide))
    have L : bytesAt s₂.mem K 16 = ciphAt s₀.mem W R (Spec.Cmac.zeros 16) := by
      rw [c.out, cipher_bytes, schB, h₁.mem, Proof.Cmac.zero2_bytes]
    have b3 : bytesAt s₃.mem K 16 = Spec.Cmac.dbl 16 (bytesAt s₂.mem K 16) := by
      have := dblMem_bytes s₂.mem K 0 0
      rw [BitVec.add_zero] at this; rw [mem₃, this]
    have b4lo : bytesAt s₄.mem K 16 = bytesAt s₃.mem K 16 :=
      Proof.Cmac.bytesAt_frame16 (by rw [mem₄]; exact dblMem_frame _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base K (by decide) (by omega_arith)).symm
    have b4hi : bytesAt s₄.mem (K + BitVec.ofNat 64 16) 16 = Spec.Cmac.dbl 16 (bytesAt s₃.mem K 16) := by
      have := dblMem_bytes s₃.mem K 0 16
      rw [BitVec.add_zero] at this; rw [mem₄, this]
    rw [r₅.mem, hK, bytesAt_32, b4lo, b4hi, b3, L, hW, hR]
    rfl

end VG.Proof.CmacAes.PPC64LE
