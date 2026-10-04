import VerifiedGarbage.Proof.Aes.X86.AesNi.Blocks
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Aes.Contract

/-!
# AES-NI on x86 (32-bit): `vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.X86.AesNi.encryptBlocks` and `decryptBlocks` against the contracts
of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, through the
per-target contract of the bitsliced implementation (`Proof.Aes.blocksX86`).
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ argOp aes aesDec blocksPrologue blocksCmp blocksRestore blocksTail imcKeys
  encryptBlocks decryptBlocks)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd
  addr_add part_contains part_sub_reg part_sub reg_contains in_reg rd_wr_ne blocksτ₀ blocks_agree₀)
open VG.X86.Wp (wp_ldm wp_stm wp_cmpi toNat_ofNat_lt)
open VG.Proof.Aes.X86.AesNi.Ecb

namespace Ecb

theorem arg_eq' (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

/-! ## The prologue -/

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  eax : s.gpr .eax = bSchP s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = bScrP s₀
  esi : s.gpr .esi = bDatP s₀
  edi : s.gpr .edi = arg s₀ 3
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨addr (bScrP s₀) 0, 8⟩] s₀.mem s.mem
  savedEsi : s.mem.readW (addr (bScrP s₀) 0) 32 = s₀.gpr .esi
  savedEdi : s.mem.readW (addr (bScrP s₀) 4) 32 = s₀.gpr .edi

theorem prologue_ok {s₀ : State} (hp : BPre s₀) : WP isa (.block blocksPrologue) s₀ (P1 s₀) := by
  have fB := hp.fB; have fSp := hp.fSp
  let B := bScrP s₀
  let E := s₀.gpr .esp
  have hwB : reg32 B 2048 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hrA : bArgR s₀ ∈ s₀.rd := by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have argC : ∀ i < 5, (bArgR s₀).Contains (addr E (4 + 4 * i)) 4 := fun i hi => by
    show (⟨addr E 4, 20⟩ : Region).Contains _ _
    exact part_contains (N := 24) (by omega) (by omega) (by omega) (by omega) (by decide)
  have argIn : ∀ (t : State), t.rd = s₀.rd → ∀ i < 5, InRegions (t.rd ++ t.wr) (addr E (4 + 4 * i)) 4 :=
    fun t ht i hi => ⟨bArgR s₀, List.mem_append_left _ (ht ▸ hrA), argC i hi⟩
  have hm : (⟨addr B 0, 8⟩ : Region) ∈ [⟨addr B 0, 8⟩] := List.mem_singleton_self _
  have dA : ∀ r ∈ [(⟨addr B 0, 8⟩ : Region)], (bArgR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.aB.sub_right (part_sub_reg fB (by omega))
  refine wp_ldm (B := E) (o := 20) rfl (argIn _ rfl 4 (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .edx = B := by rw [u₁.gpr]; rfl
  refine wp_stm (B := B) (o := 0) e₁ (by rw [u₁.wr]; exact in_reg hwB fB (by omega) (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (B := B) (o := 4) ((congrFun u₂.gpr _).trans e₁)
    (by rw [u₂.wr, u₁.wr]; exact in_reg hwB fB (by omega) (by decide))
    fun s₃ u₃ => ?_
  have esp₃ : s₃.gpr .esp = E := by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have f₃ : Frame [⟨addr B 0, 8⟩] s₀.mem s₃.mem := by
    rw [u₃.mem, u₂.mem, u₁.mem]
    exact ((Frame.refl _ _).writeW hm _ (part_contains fB (by omega) (by omega) (by omega) (by decide))).writeW
      hm _ (part_contains fB (by omega) (by omega) (by omega) (by decide))
  have a₃ : ∀ i < 5, s₃.mem.readW (addr E (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    f₃.readW (argC i hi) dA (by decide)
  refine wp_ldm (B := E) (o := 4) esp₃ (argIn _ rd₃ 0 (by omega)) fun s₄ u₄ => ?_
  refine wp_ldm (B := E) (o := 8) (by rw [u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₄.rd, u₄.wr]; exact argIn _ rd₃ 1 (by omega)) fun s₅ u₅ => ?_
  refine wp_ldm (B := E) (o := 12) (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact argIn _ rd₃ 2 (by omega)) fun s₆ u₆ => ?_
  refine wp_ldm (B := E) (o := 16)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]; exact esp₃)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact argIn _ rd₃ 3 (by omega)) fun s₇ u₇ =>
    WP.block_nil ?_
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have esi₀ : s₂.mem.readW (addr B 0) 32 = s₀.gpr .esi := by
    rw [u₂.mem, u₁.other _ (by decide), Mem.readW_writeW_self32]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃], by rw [m₇]; exact f₃, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    exact a₃ 0 (by omega)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem]
    exact a₃ 1 (by omega)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.gpr]; exact e₁
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]
    exact a₃ 2 (by omega)
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem]
    exact a₃ 3 (by omega)
  · rw [u₇.other r h5, u₆.other r h4, u₅.other r h2, u₄.other r h1, u₃.gpr, u₂.gpr, u₁.other r h3]
  · rw [m₇, u₃.mem, rd_wr_ne fB _ _ (N := 2048) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact esi₀
  · rw [m₇, u₃.mem, u₂.gpr, u₁.other _ (by decide), Mem.readW_writeW_self32]

/-! ## What the transformations need -/

theorem sch_frame {s₀ : State} (hp : BPre s₀) {m : Mem} (hf : Frame [bDatR s₀, bScrR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m ((bSchP s₀).setWidth 64) (16 * (bRounds s₀ + 1)) = sch s₀ := by
  have hn : 16 * (bRounds s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨(bSchP s₀).setWidth 64, 16 * (bRounds s₀ + 1)⟩) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dSD.sub_left (Region.sub_prefix hn)
    · exact hp.dSB.sub_left (Region.sub_prefix hn)) (by change 16 * (bRounds s₀ + 1) ≤ 2 ^ 64; omega) hi

/-- The readable round keys and their standard byte representation. -/
theorem keys_of {s₀ s : State} (hp : BPre s₀) (heax : s.gpr .eax = bSchP s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hf : Frame [bDatR s₀, bScrR s₀] s₀.mem s.mem) :
    Keys (bRounds s₀) (sch s₀) s := by
  have hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have he : ∀ j ≤ bRounds s₀, s.ea (at_ .eax (16 * j)) =
      (bSchP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j) := by
    intro j hj
    rw [ea_at, heax]
    exact addr_eq (by have h := hp.fS; omega)
  refine ⟨hnr, fun j hj => ?_, fun j hj => ?_⟩
  · rw [he j hj, hrd, hwr]
    exact ⟨bSchR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩
  · rw [he j hj, ← sch_frame hp hf]
    have h := byte_roundKey s.mem ((bSchP s₀).setWidth 64) (L := 16 * (bRounds s₀ + 1)) (j := j) (by omega)
    rw [ofInt_natCast] at h
    exact h

/-- What encryption needs, from `s₀`. -/
def KPe (s₀ : State) (s : State) : Prop :=
  Keys (bRounds s₀) (sch s₀) s ∧ s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) ∧ s.gpr .eax = bSchP s₀

/-- What decryption needs, from `s₀`. -/
def KPd (s₀ : State) (s : State) : Prop :=
  DKeys (bRounds s₀) (sch s₀) s ∧ s.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) ∧ s.gpr .eax = bSchP s₀ ∧
    s.gpr .edx = bScrP s₀

theorem keys_stable {nr : Nat} {w : List Byte} {s₀ s s' : State} (hp : BPre s₀) (hK : Keys nr w s)
    (hle : 16 * nr + 16 ≤ 240) (heax : s.gpr .eax = bSchP s₀)
    (hg : s'.gpr .eax = s.gpr .eax) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [bDatR s₀] s.mem s'.mem) : Keys nr w s' := by
  have he : ∀ j ≤ nr, s'.ea (at_ .eax (16 * j)) = s.ea (at_ .eax (16 * j)) := fun j _ => by
    rw [ea_at, ea_at, hg]
  refine ⟨hK.le, fun j hj => by rw [he j hj, hrd, hwr]; exact hK.keys j hj, fun j hj i hi => ?_⟩
  rw [he j hj, ← hK.bytes j hj i hi, ea_at, heax]
  congr 1
  exact hf.readW (r := ⟨addr (bSchP s₀) (16 * j), 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.dSD.sub_left (part_sub_reg hp.fS (by omega))).symm.symm) (by decide)

theorem kpe_stable {s₀ : State} (hp : BPre s₀) : Stable (KPe s₀) s₀ := fun s s' ⟨hK, hc, ha⟩ hg hrd hwr hf => by
  have hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  exact ⟨keys_stable hp hK (by omega) ha (hg _ (by decide) (by decide)) hrd hwr hf,
    by rw [hg _ (by decide) (by decide), hc], by rw [hg _ (by decide) (by decide), ha]⟩

theorem kpd_stable {s₀ : State} (hp : BPre s₀) : Stable (KPd s₀) s₀ :=
  fun s s' ⟨hK, hc, ha, hd⟩ hg hrd hwr hf => by
  have hnr : bRounds s₀ ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have fB := hp.fB
  have hedx : s'.gpr .edx = s.gpr .edx := hg _ (by decide) (by decide)
  have he : ∀ o, s'.ea (at_ .edx o) = s.ea (at_ .edx o) := fun o => by rw [ea_at, ea_at, hedx]
  have hm : ∀ o, 16 ≤ o → o + 16 ≤ 240 →
      s'.mem.readW (s.ea (at_ .edx o)) 128 = s.mem.readW (s.ea (at_ .edx o)) 128 := fun o h1 h2 => by
    rw [ea_at, hd]
    exact hf.readW (r := ⟨addr (bScrP s₀) o, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.dDB.sub_right (part_sub_reg fB (by omega))).symm) (by decide)
  refine ⟨⟨keys_stable hp hK.keys (by omega) ha (hg _ (by decide) (by decide)) hrd hwr hf,
    fun j h1 h2 => ?_, ?_⟩, by rw [hg _ (by decide) (by decide), hc], by rw [hg _ (by decide) (by decide), ha],
    by rw [hedx, hd]⟩
  · obtain ⟨hin, hst⟩ := hK.imc j h1 h2
    exact ⟨by rw [he, hrd, hwr]; exact hin, by rw [he, hm _ (by omega) (by omega)]; exact hst⟩
  · obtain ⟨hin, hb⟩ := hK.last
    exact ⟨by rw [he, hrd, hwr]; exact hin, by rw [he, hm _ (by omega) (by omega)]; exact hb⟩

theorem aes_blkOk {s₀ : State} (hp : BPre s₀) :
    BlkOk aes (Spec.Aes.cipher (bRounds s₀) (sch s₀)) (KPe s₀) :=
  fun rs hrs s ⟨hK, hc, _⟩ => by
    obtain ⟨hnd, h6⟩ := regs_nodup rs hrs
    exact aes_ok rs hnd h6 hp.rounds s hK hc

theorem aesDec_blkOk {s₀ : State} (hp : BPre s₀) :
    BlkOk aesDec (Spec.Aes.invCipher (bRounds s₀) (sch s₀)) (KPd s₀) :=
  fun rs hrs s ⟨hK, hc, _, _⟩ => by
    obtain ⟨hnd, h6⟩ := regs_nodup rs hrs
    exact aesDec_ok rs hnd h6 hp.rounds s hK hc

/-! ## The epilogue -/

/-- From the state after the loops, the restore and the postcondition. -/
theorem finish_ok {F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
    {s₀ s₁ s : State} (hp : BPre s₀) (h₁ : P1 s₀ s₁) {m₁ : Mem}
    (hm₁ : Frame [⟨addr (bScrP s₀) 16, 224⟩] s₁.mem m₁)
    (hI : Inv KP (F (bRounds s₀) (sch s₀)) s₀ s₁.gpr m₁ (bN s₀) (bN s₀) s) :
    WP isa (.block blocksRestore) s fun s' =>
      abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 F).post s₀ s' := by
  have fB := hp.fB
  have hscr : reg32 (bScrP s₀) 2048 ∈ s.rd ++ s.wr := by
    rw [hI.rd, hI.wr, hp.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hedx : s.gpr .edx = bScrP s₀ := by rw [hI.gpr _ (by decide) (by decide), h₁.edx]
  -- The scratch buffer's first eight bytes are as the prologue left them.
  have hsv : ∀ o, o + 4 ≤ 8 → s.mem.readW (addr (bScrP s₀) o) 32 = s₁.mem.readW (addr (bScrP s₀) o) 32 :=
    fun o ho => by
      rw [hI.frame.readW (r := ⟨addr (bScrP s₀) o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.dDB.sub_right (part_sub_reg fB (by omega))).symm) (by decide)]
      exact hm₁.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact part_disj fB (by omega) (by omega) (.inl (by omega))) (by decide)
  refine wp_ldm (B := bScrP s₀) (o := 0) hedx (in_reg hscr fB (by omega) (by decide)) fun s₂ u₂ => ?_
  refine wp_ldm (B := bScrP s₀) (o := 4) (by rw [u₂.other _ (by decide)]; exact hedx)
    (by rw [u₂.rd, u₂.wr]; exact in_reg hscr fB (by omega) (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem]
  -- Everything written since the entry: the scratch buffer and the data.
  have G : Frame [bDatR s₀, bScrR s₀] s₀.mem s₃.mem := by
    rw [hm₃]
    refine (h₁.frame.sub fun r hr => ⟨bScrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩).trans
      ((hm₁.sub fun r hr => ⟨bScrR s₀, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩).trans
      (hI.frame.mono fun r hr => by simp at hr; simp [hr]))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [u₃.other _ (by decide), u₂.gpr, hsv 0 (by omega), h₁.savedEsi]
    · rw [u₃.gpr, u₂.mem, hsv 4 (by omega), h₁.savedEdi]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), hI.gpr _ (by decide) (by decide),
        h₁.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · refine G.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.rD
    · exact hp.rB
  · show Spec.Aes.statesAt s₃.mem ((bDatP s₀).setWidth 64) (bN s₀) = _
    rw [hm₃]
    simp only [Spec.Aes.statesAt, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk := List.mem_range.mp hk
    have := hI.blocks k hk
    simp only [hk, ite_true] at this
    exact this

/-! ## The two functions -/

theorem encrypt_correct {s₀ : State} (hp : BPre s₀) :
    WP isa encryptBlocks s₀ fun s' =>
      abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 Spec.Aes.cipher).post s₀ s' := by
  have fD := hp.fD
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok hp) fun s₁ h₁ => ?_
  refine wp_cmpi fun s₂ u₂ hcf _ => WP.block_nil ?_
  have hf₁ : Frame [bDatR s₀, bScrR s₀] s₀.mem s₁.mem := h₁.frame.sub fun r hr => ⟨bScrR s₀, by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg hp.fB (by omega)⟩
  have hI₂ : Inv (KPe s₀) (Spec.Aes.cipher (bRounds s₀) (sch s₀)) s₀ s₁.gpr s₁.mem 0 0 s₂ :=
    { le := Nat.zero_le _
      kp := ⟨keys_of hp (by rw [u₂.gpr]; exact h₁.eax) (by rw [u₂.rd, h₁.rd]) (by rw [u₂.wr, h₁.wr])
          (by rw [u₂.mem]; exact hf₁), by rw [u₂.gpr, h₁.ecx, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by rw [u₂.gpr]; exact h₁.eax⟩
      gpr := fun r _ _ => by rw [u₂.gpr]
      esi := by rw [u₂.gpr, h₁.esi]; simp
      edi := by rw [u₂.gpr, h₁.edi]; simp [bN]
      frame := by rw [u₂.mem]; exact Frame.refl _ _
      blocks := fun k hk => by
        simp only [Nat.not_lt_zero, ite_false, orig]
        rw [u₂.mem, stateAt_eq, stateAt_eq]
        exact congrArg st <| h₁.frame.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128)
          (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hp.dDB.sub_left (Offset.sub_base _ (by omega))).sub_right
              (part_sub_reg hp.fB (by omega))) (by decide)
      rd := by rw [u₂.rd, h₁.rd]
      wr := by rw [u₂.wr, h₁.wr] }
  have hcf' : s₂.cf = some (decide (bN s₀ - 0 < 6)) := by
    rw [hcf, h₁.edi, Nat.sub_zero]; rfl
  refine WP.seq (WP.mono (tail_ok hp (kpe_stable hp) (aes_blkOk hp) hI₂ hcf') fun s hI => ?_)
  exact finish_ok (KP := KPe s₀) hp h₁ (Frame.refl _ _) hI

theorem dkeys_congr {nr : Nat} {w : List Byte} {s s' : State} (h : DKeys nr w s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    DKeys nr w s' := by
  have he : ∀ m, s'.ea m = s.ea m := fun m => by simp only [State.ea, hg]
  exact ⟨⟨h.keys.le, fun j hj => by rw [he, hrd, hwr]; exact h.keys.keys j hj,
      fun j hj => by rw [he, hm]; exact h.keys.bytes j hj⟩,
    fun j h1 h2 => by rw [he, hrd, hwr, hm]; exact h.imc j h1 h2,
    by rw [he, hrd, hwr, hm]; exact h.last⟩

theorem decrypt_correct {s₀ : State} (hp : BPre s₀) :
    WP isa decryptBlocks s₀ fun s' =>
      abiPreserved s₀ s' ∧ (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s₀ s' := by
  have fD := hp.fD; have fB := hp.fB
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hf₁ : Frame [bDatR s₀, bScrR s₀] s₀.mem s₁.mem := h₁.frame.sub fun r hr => ⟨bScrR s₀, by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩
  have hs : ImcSetup s₁ :=
    { sch := by rw [h₁.eax, h₁.rd, hp.rd]; exact List.mem_append_left _ (List.mem_cons_self ..)
      scr := by rw [h₁.edx, h₁.wr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      fitS := by rw [h₁.eax]; exact hp.fS
      fitB := by rw [h₁.edx]; exact fB
      sep := by rw [h₁.eax, h₁.edx]; exact hp.dSB }
  have hK₁ : Keys (bRounds s₀) (sch s₀) s₁ := keys_of hp h₁.eax h₁.rd h₁.wr hf₁
  have hc₁ : s₁.gpr .ecx = BitVec.ofNat 32 (bRounds s₀) := by
    rw [h₁.ecx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (imcKeys_ok hs hp.rounds hc₁) fun s₂ hd₂ => ?_)
  have hK₂ := dKeys_of_imc hs hK₁ hd₂
  obtain ⟨S, hI₂, -, -⟩ := hd₂
  have hm₂ : Frame [⟨addr (bScrP s₀) 16, 224⟩] s₁.mem s₂.mem := by rw [← h₁.edx]; exact hI₂.frame
  refine WP.seq (wp_cmpi fun s₃ u₃ hcf _ => WP.block_nil ?_)
  have hI₃ : Inv (KPd s₀) (Spec.Aes.invCipher (bRounds s₀) (sch s₀)) s₀ s₁.gpr s₂.mem 0 0 s₃ :=
    { le := Nat.zero_le _
      kp := ⟨dkeys_congr hK₂ u₃.gpr u₃.mem u₃.rd u₃.wr,
        by rw [u₃.gpr, hI₂.gpr, hc₁], by rw [u₃.gpr, hI₂.gpr, h₁.eax], by rw [u₃.gpr, hI₂.gpr, h₁.edx]⟩
      gpr := fun r _ _ => by rw [u₃.gpr, hI₂.gpr]
      esi := by rw [u₃.gpr, hI₂.gpr, h₁.esi]; simp
      edi := by rw [u₃.gpr, hI₂.gpr, h₁.edi]; simp [bN]
      frame := by rw [u₃.mem]; exact Frame.refl _ _
      blocks := fun k hk => by
        simp only [Nat.not_lt_zero, ite_false, orig]
        rw [u₃.mem, stateAt_eq, stateAt_eq]
        have G : Frame [bScrR s₀] s₀.mem s₂.mem :=
          (h₁.frame.sub fun r hr => ⟨bScrR s₀, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩).trans
          (hm₂.sub fun r hr => ⟨bScrR s₀, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact part_sub_reg fB (by omega)⟩)
        exact congrArg st <| G.readW (r := ⟨bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.dDB.sub_left (Offset.sub_base _ (by omega))) (by decide)
      rd := by rw [u₃.rd, hI₂.rd, h₁.rd]
      wr := by rw [u₃.wr, hI₂.wr, h₁.wr] }
  have hcf' : s₃.cf = some (decide (bN s₀ - 0 < 6)) := by
    rw [hcf, hI₂.gpr, h₁.edi, Nat.sub_zero]; rfl
  refine WP.seq (WP.mono (tail_ok hp (kpd_stable hp) (aesDec_blkOk hp) hI₃ hcf') fun s hI => ?_)
  exact finish_ok (KP := KPd s₀) hp h₁ hm₂ hI

end Ecb

end VG.Proof.Aes.X86.AesNi

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86
open VG.Proof.Aes.X86 (BPre blocksτ₀ blocks_agree₀ blocksSat)

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.cipher).post s s' :=
  (Ecb.encrypt_correct (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86 Spec.Aes.invCipher).post s s' :=
  (Ecb.decrypt_correct (BPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.cipher).pub Impl.Aes.X86.AesNi.encryptBlocks :=
  VG.Taint.constantTime (A := sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86 Spec.Aes.invCipher).pub Impl.Aes.X86.AesNi.decryptBlocks :=
  VG.Taint.constantTime (A := sseTaint) blocksτ₀ (fun _ _ h₁ h₂ hp => blocks_agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem encryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.AesNi.encryptBlocks (Spec.Aes.encryptBlocksContract X86.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86.target Impl.Aes.X86.AesNi.decryptBlocks (Spec.Aes.decryptBlocksContract X86.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct
    (by
      have a0 : arg blocksSat 0 = 0x1000 := by decide
      have a1 : arg blocksSat 1 = 10 := by decide
      have a2 : arg blocksSat 2 = 0x3000 := by decide
      have a3 : arg blocksSat 3 = 0 := by decide
      have a4 : arg blocksSat 4 = 0x4000 := by decide
      have e : argAddr blocksSat 0 = 0x8004 := by decide
      have esp : blocksSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Aes.blocksX86] [a0, a1, a2, a3, a4, e, esp] using blocksSat)

end VG.Proof.Aes.X86.AesNi
