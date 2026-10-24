module

public import VerifiedGarbage.Proof.CmacAes.PPC64LE.FinSteps
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacAes.PPC64LE.Subkeys
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.CmacAes.PPC64LE.Contract

/-!
# AES-CMAC on PPC64LE: `vg_cmac_aes_finalize`

The return address and `r14` saved (`Spill.save_ok`), the last block `Mₙ`
formed in the scratch buffer (`full_wp` for a complete block, `partial_wp`
for a partial one, `BPost`), XORed into the state (`finArgs_wp`), the state
enciphered in place, and the registers restored: `CIPH_K(Cₙ₋₁ ⊕ Mₙ)`, the
MAC (`Proof.Cmac.macFull_split`), as on AArch64
(`Proof/CmacAes/AArch64/FinalizeCorrect.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacAes.PPC64LE
open VG.Proof.AesCbc.PPC64LE (CallPre blk_call in_rw)
open VG.Spec.Aes (bytesAt)

/-- The precondition, by name: the key (schedule and subkeys) `W`, the state
`St`, the last bytes `P` (`L` of them), the scratch buffer `S` and the
rounds `R`. -/
structure FPre (s₀ : State) (W St P S : Addr) (L R : Nat) : Prop where
  r3 : s₀.gpr .r3 = W
  r5 : s₀.gpr .r5 = St
  r6 : s₀.gpr .r6 = P
  r7 : (s₀.gpr .r7).toNat = L
  r8 : s₀.gpr .r8 = S
  r4 : (s₀.gpr .r4).toNat = R
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

theorem FPre.of {s₀ : State} (h : finalizePPC64LE.pre s₀) :
    FPre s₀ (s₀.gpr .r3) (s₀.gpr .r5) (s₀.gpr .r6) (s₀.gpr .r8) (s₀.gpr .r7).toNat (s₀.gpr .r4).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 16 (bytesAt m (W + BitVec.ofNat 64 240) 16)
    (bytesAt m (W + BitVec.ofNat 64 256) 16) (bytesAt m P L)

/-- The memory after saving `r14` and the return address. -/
abbrev finMem (s₀ : State) (S : Addr) : Mem := Spill.saveMem s₀.mem S (s₀.write .r0 s₀.lr).gpr finSaved

theorem fin_bound : ∀ p ∈ finSaved, 2064 ≤ p.2 ∧ p.2 + 8 ≤ 2080 := by decide

/-- What the branch on the length leaves: `Mₙ` in the scratch buffer. -/
structure BPost (s₀ : State) (W St P S : Addr) (L : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = W
  r5 : s.gpr .r5 = St
  r8 : s.gpr .r8 = S
  r4 : s.gpr .r4 = s₀.gpr .r4
  keep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩] (finMem s₀ S) s.mem
  blk : bytesAt s.mem (S + BitVec.ofNat 64 2048) 16 = mn s₀.mem W P L

/-- Saving the registers changes only their slots. -/
theorem finMem_frame (s₀ : State) (S : Addr) : Frame [⟨S + BitVec.ofNat 64 2064, 16⟩] s₀.mem (finMem s₀ S) :=
  Spill.saveMem_frame (lo := 2064) (n := 16) (fun p hp' => fin_bound p hp') (by decide) _ _ _

theorem slots_scr (S : Addr) : Region.Sub ⟨S + BitVec.ofNat 64 2064, 16⟩ ⟨S, 2176⟩ := Offset.sub_base _ (by decide)

section
variable {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 2176) : InRegions s₀.wr (S + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 272) : InRegions (s₀.rd ++ s₀.wr) (W + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨W, 272⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ L) : InRegions (s₀.rd ++ s₀.wr) (P + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨P, L⟩) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

/-- The last block, from the memory after saving the registers. -/
theorem FPre.mn_fin : mn (finMem s₀ S) W P L = mn s₀.mem W P L := by
  have kS (d : Nat) (h : d + 16 ≤ 272) :
      bytesAt (finMem s₀ S) (W + BitVec.ofNat 64 d) 16 = bytesAt s₀.mem (W + BitVec.ofNat 64 d) 16 :=
    Proof.Cmac.bytesAt_frame (finMem_frame s₀ S) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (slots_scr S)) (by decide)
  rw [mn, mn, kS 240 (by decide), kS 256 (by decide), Proof.Cmac.bytesAt_frame (finMem_frame s₀ S) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.last_scr.sub_right (slots_scr S)) (by have := hp.len; omega)]

end

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem full_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L = 16)
    {s : State} (hg : ∀ r, r ≠ .r0 → r ≠ .r9 → s.gpr r = s₀.gpr r) (hm : s.mem = finMem s₀ S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  rw [full_eq, ← List.append_nil (xor2 _ _ _ _ _ _)]
  refine xor2_wp .r6 .r3 .r8 0 240 2048 (P := P) (Q := W + BitVec.ofNat 64 240) (C := S + BitVec.ofNat 64 2048)
    ⟨by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by rw [hg _ (by decide) (by decide), hp.r6, BitVec.add_zero]) (by rw [hg _ (by decide) (by decide), hp.r6])
    (by rw [hg _ (by decide) (by decide), hp.r3]) (by rw [hg _ (by decide) (by decide), hp.r3, Offset.add_add])
    (by rw [hg _ (by decide) (by decide), hp.r8]) (by rw [hg _ (by decide) (by decide), hp.r8, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by rw [hrd, hwr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inLast (d := 8) (n := 8) (by decide))
    (by rw [hrd, hwr]; exact hp.inKey (d := 240) (n := 8) (by decide))
    (by rw [hrd, hwr, Offset.add_add]; exact hp.inKey (d := 248) (n := 8) (by decide))
    (by rw [hwr]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
    fun s' g mem rd wr => wp_nil ?_
  have gg (r : Reg) (h₀ : r ≠ .r0) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) : s'.gpr r = s₀.gpr r := by
    rw [g r h₁ h₂, hg r h₀ h₁]
  refine ⟨by rw [gg _ (by decide) (by decide) (by decide), hp.r3],
    by rw [gg _ (by decide) (by decide) (by decide), hp.r5], by rw [gg _ (by decide) (by decide) (by decide), hp.r8],
    gg _ (by decide) (by decide) (by decide),
    fun r hr => gg r (preserved_ne r hr).1 (preserved_ne r hr).2.2.2.2.2.2.2.1 (preserved_ne r hr).2.2.2.2.2.2.2.2.1,
    by rw [rd, hrd], by rw [wr, hwr], by rw [mem, hm]; exact Proof.Cmac.xor2Mem_frame _ _ _ _, ?_⟩
  rw [mem, hm, Proof.Cmac.xor2Mem_bytes, ← hp.mn_fin]
  · simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
    exact Proof.Cmac.xor_comm _ _
  · exact (hp.last_scr.symm.sub_left (Offset.sub_base S (d := 2048) (n := 8) (k := 2176) (by decide))).sub_right
      (Offset.sub_base P (d := 8) (n := 8) (k := 16) (by decide))
  · rw [Offset.add_add]
    exact (hp.key_scr.symm.sub_left (Offset.sub_base S (d := 2048) (n := 8) (k := 2176) (by decide))).sub_right
      (Offset.sub_base W (d := 248) (n := 8) (k := 272) (by decide))

open VG.WriteBytes in
theorem partial_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) (hL : L < 16)
    {s : State} (hg : ∀ r, r ≠ .r0 → r ≠ .r9 → s.gpr r = s₀.gpr r) (hm : s.mem = finMem s₀ S)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have hb : L < 2 ^ 64 := by omega
  have h7 : s₀.gpr .r7 = BitVec.ofNat 64 L := by rw [← hp.r7]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 2048 = C := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, finMem s₀ S = M := ⟨_, rfl⟩
  have dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact hp.last_scr.sub_right (Offset.sub_base _ (by decide))
  have dKC (d n : Nat) (h : d + n ≤ 272) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨C, 16⟩ := by
    rw [← hC]; exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (Offset.sub_base _ (by decide))
  -- Zero the block.
  refine WP.seq (WP.mono (zero_wp (s := s) (C := C) (by rw [hg _ (by decide) (by decide), hp.r8, ← hC, cOff])
    (by rw [hg _ (by decide) (by decide), hp.r8, ← hC, Offset.add_add, cOff])
    (by rw [hwr, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
    (by rw [hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide)))
    fun s₁ ⟨mem₁, r10₁, r11₁, r12₁, g₁, rd₁, wr₁⟩ => ?_)
  have zf : s₁.mem = Proof.Cmac.zero2 M C := by rw [mem₁, hm, hM]
  have fz : Frame [⟨C, 16⟩] M (Proof.Cmac.zero2 M C) := Proof.Cmac.frame_store2 _ _ _
  have lastZ : bytesAt (Proof.Cmac.zero2 M C) P L = bytesAt M P L :=
    Proof.Cmac.bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  have g₁' (r : Reg) (h₀ : r ≠ .r0) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) (h₃ : r ≠ .r11) (h₄ : r ≠ .r12) :
      s₁.gpr r = s₀.gpr r := by rw [g₁ r h₁ h₂ h₃ h₄, hg r h₀ h₁]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
      s₂.mem = writeBytes (Proof.Cmac.zero2 M C) C (bytesAt M P L) ∧ s₂.gpr .r10 = C + BitVec.ofNat 64 L ∧
      (∀ r, r ≠ .r0 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → s₂.gpr r = s₀.gpr r) ∧
      s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := eval_zero_ofNat s₁ .r7 hb (by rw [g₁' _ (by decide) (by decide) (by decide) (by decide) (by decide), h7])
    by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [bytesAt, writeBytes_nil], by rw [r10₁]; simp,
        fun r h₀ h₁ h₂ h₃ h₄ => g₁' r h₀ h₁ h₂ h₃ h₄, by rw [rd₁, hrd], by rw [wr₁, hwr]⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_wp s₁ (P := P) (C := C) (by omega) (by omega)
        (by rw [r11₁, hg _ (by decide) (by decide), hp.r6]) r10₁
        (by rw [r12₁, hg _ (by decide) (by decide), h7])
        (fun i hi => by rw [rd₁, wr₁, hrd, hwr]; exact hp.inLast (d := i) (n := 1) (by omega))
        (fun i hi => by
          rw [wr₁, hwr, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + i) (n := 1) (by omega))
        (dPC.sub_right (Region.sub_prefix (by omega)))) ?_
      rintro s₂ ⟨m₂, r10₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], r10₂, fun r h₀ h₁ h₂ h₃ h₄ => by rw [g₂ r h₁ h₂ h₃ h₄, g₁' r h₀ h₁ h₂ h₃ h₄],
        by rw [rd₂, rd₁, hrd], by rw [wr₂, wr₁, hwr]⟩
  · obtain ⟨m₂, r10₂, g₂, rd₂, wr₂⟩ := h₂
    rw [padK2_eq, List.cons_append, List.cons_append, List.nil_append]
    refine wp_li (by decide) fun s₃ u₃ => ?_
    refine wp_stb (a := C + BitVec.ofNat 64 L) (by decide) (by decide)
      (by rw [u₃.other _ (by decide), r10₂, BitVec.add_zero])
      (by rw [u₃.wr, wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 2048 + L) (n := 1) (by omega)) fun s₄ u₄ => ?_
    have g₄ (r : Reg) (h₀ : r ≠ .r0) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) (h₃ : r ≠ .r11) (h₄ : r ≠ .r12) :
        s₄.gpr r = s₀.gpr r := by rw [u₄.gpr, u₃.other _ h₁, g₂ r h₀ h₁ h₂ h₃ h₄]
    have r8₄ : s₄.gpr .r8 = S := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r8]
    have r3₄ : s₄.gpr .r3 = W := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r3]
    have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, rd₂]
    have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, wr₂]
    rw [← List.append_nil (xor2 _ _ _ _ _ _)]
    refine xor2_wp .r8 .r3 .r8 2048 256 2048 (P := C) (Q := W + BitVec.ofNat 64 256) (C := C)
      ⟨by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
      (by rw [r8₄, hC]) (by rw [r8₄, ← hC, Offset.add_add]) (by rw [r3₄]) (by rw [r3₄, Offset.add_add])
      (by rw [r8₄, hC]) (by rw [r8₄, ← hC, Offset.add_add])
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      (by rw [rd₄, wr₄, ← hC]; exact wr_in (hp.inScr (d := 2048) (n := 8) (by decide)))
      (by rw [rd₄, wr₄, ← hC, Offset.add_add]; exact wr_in (hp.inScr (d := 2056) (n := 8) (by decide)))
      (by rw [rd₄, wr₄]; exact hp.inKey (d := 256) (n := 8) (by decide))
      (by rw [rd₄, wr₄, Offset.add_add]; exact hp.inKey (d := 264) (n := 8) (by decide))
      (by rw [wr₄, ← hC]; exact hp.inScr (d := 2048) (n := 8) (by decide))
      (by rw [wr₄, ← hC, Offset.add_add]; exact hp.inScr (d := 2056) (n := 8) (by decide))
      fun s₅ g₅ m₅ rd₅ wr₅ => wp_nil ?_
    have gg (r : Reg) (h₀ : r ≠ .r0) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) (h₃ : r ≠ .r11) (h₄ : r ≠ .r12) :
        s₅.gpr r = s₀.gpr r := by rw [g₅ r h₁ h₂, g₄ r h₀ h₁ h₂ h₃ h₄]
    have hlen : (bytesAt M P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have m₄ : s₄.mem = (writeBytes (Proof.Cmac.zero2 M C) C (bytesAt M P L)).writeW
        (C + BitVec.ofNat 64 L) (0x80 : Byte) := by
      rw [u₄.mem, u₃.gpr, u₃.mem, m₂]; rfl
    have fW : Frame [⟨C, 16⟩] (writeBytes (Proof.Cmac.zero2 M C) C (bytesAt M P L)) s₄.mem := by
      rw [m₄]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    have fB : Frame [⟨C, 16⟩] (Proof.Cmac.zero2 M C) (writeBytes (Proof.Cmac.zero2 M C) C (bytesAt M P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 16) (by omega) (by decide))
    have f₄ : Frame [⟨C, 16⟩] M s₄.mem := (fz.trans fB).trans fW
    have k2 : bytesAt s₄.mem (W + BitVec.ofNat 64 256) 16 = bytesAt M (W + BitVec.ofNat 64 256) 16 :=
      Proof.Cmac.bytesAt_frame16 f₄ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dKC 256 16 (by decide)
    have pad : bytesAt s₄.mem C 16 = bytesAt M P L ++ [0x80] ++ Spec.Cmac.zeros (16 - L - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero2 M C) C (bytesAt M P L)
        (by rw [hlen]; exact hL) (Proof.Cmac.zero2_bytes _ _)
      rw [hlen] at this
      rw [m₄]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r3],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r5],
      by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), hp.r8],
      gg _ (by decide) (by decide) (by decide) (by decide) (by decide),
      fun r hr => gg r (preserved_ne r hr).1 (preserved_ne r hr).2.2.2.2.2.2.2.1 (preserved_ne r hr).2.2.2.2.2.2.2.2.1
        (preserved_ne r hr).2.2.2.2.2.2.2.2.2.1 (preserved_ne r hr).2.2.2.2.2.2.2.2.2.2,
      by rw [rd₅, rd₄], by rw [wr₅, wr₄], ?_, ?_⟩
    · rw [m₅, hC, hM]; exact f₄.trans (Proof.Cmac.xor2Mem_frame _ _ _ _)
    · rw [m₅, hC, Proof.Cmac.xor2Mem_bytes, pad, k2, ← hp.mn_fin, hM]
      · simp only [mn, Spec.Cmac.lastBlock, hlen, show L ≠ 16 by omega, ite_false]
        exact Proof.Cmac.xor_comm _ _
      · simpa using Offset.disjoint C (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
      · rw [Offset.add_add]
        exact (dKC 264 8 (by decide)).symm.sub_left (Region.sub_prefix (by decide))

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ : State) (W St P S : Addr) (L R : Nat) (s : State) : Prop where
  pre : CallPre s W St S R
  r14 : s.gpr .r14 = S
  keep : ∀ r ∈ preserved, r ≠ .r14 → s.gpr r = s₀.gpr r
  frame : Frame [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩] (finMem s₀ S) s.mem
  st : bytesAt s.mem St 16 = Spec.Cmac.xor (bytesAt s₀.mem St 16) (mn s₀.mem W P L)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) {s : State}
    (h : BPost s₀ W St P S L s) : WP isa (.block finArgs) s (FMid s₀ W St P S L R) := by
  have sw := hp.scr_wrap
  have tw := hp.st_wrap
  have hRegs : s.rd ++ s.wr = [⟨W, 272⟩, ⟨P, L⟩, ⟨St, 16⟩, ⟨S, 2176⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have inC (d : Nat) (hd : d + 8 ≤ 2176) : InRegions s.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [h.wr]; exact hp.inScr (by omega)
  have inSt (d : Nat) (hd : d + 8 ≤ 16) : InRegions s.wr (St + BitVec.ofNat 64 d) 8 := by
    rw [h.wr, hp.wr]; exact in_rw (r := ⟨St, 16⟩) (by simp) (Offset.contains_base _ hd (by omega))
  have dCSt : (⟨S + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint ⟨St, 16⟩ :=
    hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  rw [finArgs_eq]
  refine xor2_wp .r5 .r8 .r5 0 2048 0 (P := St) (Q := S + BitVec.ofNat 64 2048) (C := St)
    ⟨by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by rw [h.r5, BitVec.add_zero]) (by rw [h.r5]) (by rw [h.r8]) (by rw [h.r8, Offset.add_add])
    (by rw [h.r5, BitVec.add_zero]) (by rw [h.r5])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (by simpa using wr_in (inSt 0 (by decide))) (wr_in (inSt 8 (by decide)))
    (wr_in (inC 2048 (by decide))) (by rw [Offset.add_add]; exact wr_in (inC 2056 (by decide)))
    (by simpa using inSt 0 (by decide)) (inSt 8 (by decide)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  unfold Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => wp_mr fun s₄ u₄ => wp_nil ?_
  have g (r : Reg) (h₁ : r ≠ .r9) (h₂ : r ≠ .r10) (h₃ : r ≠ .r14) (h₄ : r ≠ .r6) (h₅ : r ≠ .r7) :
      s₄.gpr r = s.gpr r := by
    rw [u₄.other _ h₅, u₃.other _ h₄, u₂.other _ h₃, g₁ r h₁ h₂]
  have r14₄ : s₄.gpr .r14 = S := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide) (by decide), h.r8]
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  have m₄ : s₄.mem = Proof.Cmac.xor2Mem s.mem St St (S + BitVec.ofNat 64 2048) := by
    rw [u₄.mem, u₃.mem, u₂.mem, m₁]
  have stS : bytesAt s.mem St 16 = bytesAt s₀.mem St 16 := by
    rw [Proof.Cmac.bytesAt_frame16 h.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dCSt.symm]
    exact Proof.Cmac.bytesAt_frame16 (finMem_frame s₀ S) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr.sub_right (slots_scr S)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hp.rounds, hp.key_st.sub_left (Region.sub_prefix (by decide)),
    (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
    hp.st_scr.sub_right (Region.sub_prefix (by decide)), hp.st_wrap, ?_, ?_⟩, r14₄, fun r hr h14 => ?_, ?_, ?_,
    rd₄, wr₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r3]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r4, ← hp.r4, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [u₄.other _ (by decide), u₃.gpr]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide) (by decide), h.r8]
  · rw [rd₄, wr₄, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨W, 272⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₄, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨St, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2176⟩, by simp, 0, by simp, by simp⟩
  · obtain ⟨-, -, -, -, h6, h7, -, h9, h10, -⟩ := preserved_ne r hr
    rw [g r h9 h10 h14 h6 h7, h.keep r hr]
  · rw [m₄]
    exact (h.frame.mono (by simp)).trans ((Proof.Cmac.xor2Mem_frame _ _ _ _).mono (by simp))
  · rw [m₄, Proof.Cmac.xor2Mem_bytes, stS, h.blk]
    · simpa using Offset.disjoint St (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by omega)
    · exact (hp.st_scr.sub_left (Region.sub_prefix (by decide))).sub_right
        (by rw [Offset.add_add]; exact Offset.sub_base _ (by decide))

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R) :
    WP isa finPre s₀ (FMid s₀ W St P S L R) := by
  have h7 : s₀.gpr .r7 = BitVec.ofNat 64 L := by rw [← hp.r7]; apply BitVec.eq_of_toNat_eq; simp
  have A : WP isa (.block (finSave ++ [.subi .r9 .r7 16])) s₀ fun s =>
      isa.eval (.zero .d .r9) s = some (decide (L = 16)) ∧ (∀ r, r ≠ .r0 → r ≠ .r9 → s.gpr r = s₀.gpr r) ∧
      s.mem = finMem s₀ S ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
    rw [finSave_eq, List.cons_append]
    refine WP.cons exec_mflr (Spill.save_ok (b := .r8) (l := finSaved) (by decide) (by decide) (fun p hp' => ?_) ?_)
    · have := fin_bound p hp'
      show InRegions s₀.wr (s₀.gpr .r8 + BitVec.ofNat 64 p.2) 8
      rw [hp.r8]; exact hp.inScr (by omega)
    have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, hr]
    refine WP.mono (sub16_wp (L := L) (by rw [g₀ _ (by decide), h7]) hp.len) fun s₁ ⟨ev, g, m, rd, wr⟩ =>
      ⟨ev, fun r h0 h9 => by rw [g r h9]; exact g₀ r h0, ?_, rd, wr⟩
    rw [m]; show Spill.saveMem _ _ _ _ = _; rw [g₀ .r8 (by decide), hp.r8]; rfl
  refine WP.seq (WP.mono A fun s₁ ⟨ev₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀ W St P S L) ?_ fun _ h => finArgs_wp hp h)
  by_cases hL : L = 16
  · exact WP.ite true (by rw [ev₁]; simp [hL]) (fun _ => full_wp hp hL g₁ m₁ rd₁ wr₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) g₁ m₁ rd₁ wr₁)

theorem finalize_wp {s₀ : State} (h0 : finalizePPC64LE.pre s₀) :
    WP isa finalize s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      finalizePPC64LE.post s₀ s' := by
  have hp := FPre.of h0
  generalize hW : s₀.gpr .r3 = W at hp
  generalize hSt : s₀.gpr .r5 = St at hp
  generalize hP : s₀.gpr .r6 = P at hp
  generalize hS : s₀.gpr .r8 = S at hp
  generalize hL : (s₀.gpr .r7).toNat = L at hp
  generalize hR : (s₀.gpr .r4).toNat = R at hp
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have sw := hp.scr_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
    AesCbc.PPC64LE.encryptBlocks_noFrames h₁.pre) fun s₂ c => ?_)
  have slotD : ∀ p ∈ finSaved, ∀ r ∈ [⟨S + BitVec.ofNat 64 2048, 16⟩, ⟨St, 16⟩, ⟨S, 2048⟩],
      Region.Disjoint ⟨S + BitVec.ofNat 64 p.2, 8⟩ r := by
    intro p hp' r hr
    have hb := fin_bound p hp'
    have hsub : Region.Sub ⟨S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 2176⟩ := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact hp.st_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)
  have hsv : Spill.Saved S (s₀.write .r0 s₀.lr).gpr finSaved s₂.mem :=
    ((Spill.saveMem_saved (by decide) s₀.mem S _).frame h₁.frame fun p hp' r hr =>
      slotD p hp' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inl rfl
        · exact .inr (.inl rfl))).frame
      c.frame fun p hp' r hr => slotD p hp' r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr rfl))
  have r14₂ : s₂.gpr .r14 = S := by rw [c.saved _ (by decide), h₁.r14]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, h₁.rd, h₁.wr]
  rw [show finSaved.map (fun (r, d) => Instr.load .d r .r14 d) = Spill.restoreCode .r14 finSaved from rfl]
  refine Spill.restore_ok (b := .r14) (l := finSaved) (by decide) r14₂ (by decide) (by decide)
    (fun p hp' => ?_) hsv fun s₃ r₃ => WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, ?_⟩)
  · have := fin_bound p hp'
    rw [rdwr₂]; exact wr_in (hp.inScr (by omega))
  · show s₃.gpr r = _
    have h0 : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by simp [State.write, (preserved_ne r hr).1]
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases h14 : r = .r14
    · left; subst h14; decide
    · right; rw [c.saved r hr, h₁.keep r hr h14, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, 2064) (by decide)]; simp [State.write]
  · intro hk msg hm hne hst
    rw [hW, hR] at hk hst ⊢
    rw [hSt] at hst ⊢
    rw [hL] at hne
    rw [hP, hL]
    have sch : bytesAt s₁.mem W (16 * (R + 1)) = bytesAt s₀.mem W (16 * (R + 1)) := by
      rw [Proof.Cmac.bytesAt_frame h₁.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by decide))
          · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)]
      exact Proof.Cmac.bytesAt_frame (finMem_frame s₀ S) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.key_scr.sub_left (Region.sub_prefix (by omega))).sub_right (slots_scr S)) (by omega)
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk
    rw [r₃.mem, c.out, cipher_bytes, sch, h₁.st, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne)]

end VG.Proof.CmacAes.PPC64LE
