module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPd
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcCrt
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Rsa.Scratch

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: the call of `vg_rsa_public_precomputed_checked`

`r₁` kept in its slot, and `M^e mod n` written to `out` from `n`'s values,
the first words of `pre` (`pdP_call`), for whatever `M` holds.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivCheckedPc
open VG.Impl.Rsa.X86_64.PrivChecked (sp lea oM)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem argP_in {s t : State} (hp : PreFPc s) (he : EnvP s t) {j : Nat} (hj : j < 16) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 128⟩, List.mem_append_left _ (by
    rw [he.rd, hp.hrd]; simp only [List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))))))),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- A stack argument past a store to the frame. -/
theorem argP_wo {s : State} (m : Mem) {d : Nat} (v : BitVec 64) (hd : d + 8 ≤ frameBytes) {j : Nat} (hj : j < 16) :
    (m.writeW (off (fbP s) d) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  rw [stackArgAddr_fbP]
  exact word_wo m (fbP s) v (by unfold frameBytes at *; omega) (by unfold frameBytes at *; omega)
    (by unfold frameBytes; omega)

theorem argP_wo0 {s : State} (m : Mem) (v : BitVec 64) {j : Nat} (hj : j < 16) :
    (m.writeW (fbP s) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  have := argP_wo (s := s) m v (d := 0) (by decide) hj
  simpa only [off, BitVec.add_zero] using this

/-- `r₁` kept, and the arguments of `vg_rsa_public_precomputed_checked`. -/
theorem pdArgsP_ok {s t : State} (hp : PreFPc s) (he : EnvP s t) :
    WP isa (.block pdArgs) t fun t' => EnvP s t' ∧
      t'.mem = (((((t.mem.writeW (off (fbP s) oR1) (t.gpr .rax)).writeW (fbP s) (off (fbP s) oM)).writeW
        (off (fbP s) 8) (s.gpr .rcx)).writeW (off (fbP s) 16) (stackArg s 12)).writeW (off (fbP s) 24)
          (stackArg s 13)) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = stackArg s 14 ∧
      t'.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 := by
  have hs := he.scr hp
  have hk2 := hp.k2
  have h0 : InRegions t.wr (fbP s) 8 := by simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t' =>
      t'.mem = (((((t.mem.writeW (off (fbP s) oR1) (t.gpr .rax)).writeW (fbP s) (off (fbP s) oM)).writeW
        (off (fbP s) 8) (s.gpr .rcx)).writeW (off (fbP s) 16) (stackArg s 12)).writeW (off (fbP s) 24)
          (stackArg s 13)) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = stackArg s 14 ∧
      t'.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9) (by
    xrun [pdArgs, lea, preWords, List.cons_append, List.nil_append, ea_sp, he.rsp, arg,
      show fbP s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 12) = stackArgAddr s 12 from (stackArgAddr_fbP s 12).symm,
      show fbP s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 13) = stackArgAddr s 13 from (stackArgAddr_fbP s 13).symm,
      show fbP s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 14) = stackArgAddr s 14 from (stackArgAddr_fbP s 14).symm,
      hs.st (d := oR1) (by decide), h0, hs.st (d := 8) (by decide),
      hs.st (d := 16) (by decide), hs.st (d := 24) (by decide), hs.ld (d := oK) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oE) (by decide), hs.ld (d := oEl) (by decide),
      argP_in hp he (show 12 < 16 by decide), argP_in hp he (show 13 < 16 by decide),
      argP_in hp he (show 14 < 16 by decide),
      sx_ofNat (show oM < 2 ^ 31 by decide), word_wo, argP_wo, word_wo0, argP_wo0,
      he.sK, he.sOut, he.sE, he.sEl, he.arg hp (show 12 < 16 by decide), he.arg hp (show 13 < 16 by decide),
      he.arg hp (show 14 < 16 by decide), preWords_val (show (s.gpr .rcx).toNat ≤ 1024 by omega)]) rfl)
    fun t' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ⟨⟨?_, k.2.1.trans he.rd, k.2.2.trans he.wr, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      hm, hdi, hsi, hdx, hcx, h8, h9⟩
  · rw [k.gpr (by decide)]; exact he.rsp
  · have h0' : (⟨fbP s, frameBytes⟩ : Region).Contains (fbP s) 8 := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    have fr : ∀ {d : Nat}, d + 8 ≤ frameBytes → (⟨fbP s, frameBytes⟩ : Region).Contains (off (fbP s) d) 8 :=
      fun hd => Offset.contains_base _ hd (by unfold frameBytes at hd; omega)
    rw [hm]
    refine frameP_call he.mem (rs := [⟨fbP s, frameBytes⟩]) ?_ fun r hr => ?_
    · exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fr (d := oR1) (by decide))).writeW
        (List.mem_singleton_self _) _ h0').writeW (List.mem_singleton_self _) _ (fr (d := 8) (by decide))).writeW
        (List.mem_singleton_self _) _ (fr (d := 16) (by decide))).writeW (List.mem_singleton_self _) _
        (fr (d := 24) (by decide)))
    · rw [List.mem_singleton.mp hr]
      have := frameP_sub s (d := 0) (n := frameBytes) (by decide)
      exact .inl (by simpa only [off, BitVec.add_zero] using this)
  all_goals rw [hm]; simp (disch := decide) only [Bignum.word, word_wo, word_wo0]
  · exact he.sOut
  · exact he.sN
  · exact he.sK
  · exact he.sE
  · exact he.sEl

/-! ## The call -/

/-- `M` in the frame, `k` bytes. -/
def mRP (s : State) : Region := ⟨off (fbP s) oM, (s.gpr .rcx).toNat⟩

theorem mRP_sub {s : State} (hp : PreFPc s) : Region.Sub (mRP s) (stkRP s) :=
  frameP_sub s (by have := hp.k2; unfold oM frameBytes; omega)

/-- `pre`, and `n`'s values: its first `2 ⌈k / 8⌉` words. -/
def preFull (s : State) : Region := ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
def preRP (s : State) : Region := ⟨stackArg s 14, Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8⟩

theorem preRP_sub {s : State} (hp : PreFPc s) : Region.Sub (preRP s) (preFull s) :=
  Region.sub_prefix (by
    rw [hp.hprl]; unfold Spec.Rsa.privatePrecomputedWords; omega)

/-- What the call reads: `n`'s values, `e`, `M` and its stack arguments. -/
def pdRdP (s : State) : List Region :=
  [preRP s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, mRP s, ⟨fbP s, 32⟩]

/-- What it writes: `out` and the working space. -/
def pdWrP (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, scrR s]

/-- A region of the frame at `d`, apart from the return address of a call. -/
theorem retP_disjoint (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (below (fbP s) 8).Disjoint ⟨off (fbP s) d, n⟩ := by
  rw [show below (fbP s) 8 = ⟨kbP s, 8⟩ by simp only [below]; rw [← fbP_sub8]; rfl, fbP_off]
  exact Offset.base_disjoint _ (by omega) (by unfold frameBytes at h; omega)

theorem pdP_pre {s t : State} (hp : PreFPc s) (he : EnvP s t)
    (hw0 : word t.mem (fbP s) 0 = off (fbP s) oM) (hw1 : word t.mem (fbP s) 8 = s.gpr .rcx)
    (hw2 : word t.mem (fbP s) 16 = stackArg s 12) (hw3 : word t.mem (fbP s) 24 = stackArg s 13)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = stackArg s 14)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pdContract.pre (t.callEntry.withRegions (pdRdP s) (pdWrP s)) := by
  have hpw : Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ 256 := by
    have := hp.k2; unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (pdRdP s) (pdWrP s)) i = word t.mem (fbP s) (8 * i) :=
    fun i hi => stackArgP_entry he.rsp _ _ (by omega)
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, hcxN, stackArgAddrP_entry he.rsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), Nat.reduceMul, hw0, hw1, hw2, hw3, fbP_sub8]
  have ⟨hK1, _, _⟩ := kbP_toNat hp
  have e3 : oM = 160 := rfl
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have hfb : fbP s = kbP s + BitVec.ofNat 64 8 := fbP_kbP s
  have sP := preRP_sub hp
  have sM := mRP_sub hp
  have sA : Region.Sub ⟨fbP s, 32⟩ (stkRP s) := by
    have := frameP_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have rb : below (fbP s) 8 = ⟨kbP s, 8⟩ := by simp only [below]; rw [← fbP_sub8]; rfl
  have sR : Region.Sub ⟨kbP s, 8⟩ (stkRP s) := by rw [← rb]; exact retP_sub s
  have dRM : (⟨kbP s, 8⟩ : Region).Disjoint (mRP s) := by
    rw [← rb]; exact retP_disjoint s (by unfold oM frameBytes; omega)
  have dRA : (⟨kbP s, 8⟩ : Region).Disjoint ⟨fbP s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have dOut : ∀ {r : Region}, Region.Sub r (stkRP s) →
      (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint r := fun h => by
    rw [← hsi']; exact (hp.dKo.sub_left h).symm
  have wFr : ∀ {d n : Nat}, d + n ≤ frameBytes → (off (fbP s) d).toNat + n ≤ 2 ^ 64 := fun {d n} h => by
    unfold frameBytes at h hK1
    rw [fbP_off, ← off, toNat_off (by omega)]; omega
  have wPre := hp.wPre
  have hprl := hp.hprl
  unfold Spec.Rsa.privatePrecomputedWords at hprl
  refine ⟨by omega, rfl, rfl, ?_, ?_, dOut sM, ?_, dOut sA, hp.dpres.sub_left sP, hp.des,
    hp.dKs.sub_left sM, (hp.dKs.sub_left sA).symm, ?_, ((hp.dKpre.sub_left sR).symm.sub_left sP).symm,
    hp.dKe.sub_left sR, dRM, hp.dKs.sub_left sR, dRA,
    ?_, by omega, hp.wE, wFr (by unfold oM frameBytes; omega), hp.wS,
    ⟨hp.k1, hp.k2⟩, trivial, trivial, hp.L1, hp.L2,
    VG.Proof.Rsa.publicScratch_le ⟨hp.k1, hp.k2⟩ hp.hsl⟩
  · have h := (hp.dOpre.symm.sub_left sP).symm
    simp only [preRP] at h; rw [hsi'] at h; exact h
  · rw [← hsi']; exact hp.dOe
  · rw [← hsi']; exact hp.dOs
  · rw [← hsi']; exact (hp.dKo.sub_left sR)
  · rw [← hsi']; exact hp.wO

/-- Bytes of the frame at `d`, kept by a call's return address. -/
theorem entryP_bytes {s t : State} (hsp : t.gpr .rsp = fbP s) {d n : Nat} (h : d + n ≤ frameBytes) :
    Spec.Rsa.bytesAt t.callEntry.mem (off (fbP s) d) n = Spec.Rsa.bytesAt t.mem (off (fbP s) d) n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => (callEntryP_frame hsp).bytes (R := ⟨off (fbP s) d, n⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (retP_disjoint s h).symm)
    (by dsimp only; unfold frameBytes at h; omega) (List.mem_range.mp hi)

/-- The regions `vg_rsa_public_precomputed_checked` is given. -/
theorem pdP_covers {s t : State} (hp : PreFPc s) (he : EnvP s t) :
    Covers (pdRdP s) (t.rd ++ t.wr) ∧ Covers (pdWrP s) t.wr := by
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have hprl := hp.hprl
  unfold Spec.Rsa.privatePrecomputedWords at hprl
  have hfr : (⟨fbP s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pdWrP s) t.wr := Covers.of_mem fun r hr => by
    simp only [pdWrP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [he.wr, hp.hwr]
    rcases hr with rfl | rfl
    · rw [← hsi']; simp
    · simp [scrR]
  have cr : Covers (pdRdP s) (t.rd ++ t.wr) := Covers.of_sub fun r hr => by
    simp only [pdRdP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨stackArg s 14, (stackArg s 15).toNat * 8⟩, List.mem_append_left _ (by rw [he.rd, hp.hrd]; simp), 0,
        z _, by simp only [preRP]; omega⟩
    · exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, List.mem_append_left _ (by rw [he.rd, hp.hrd]; simp), 0, z _,
        by dsimp only; omega⟩
    · exact ⟨_, List.mem_append_right _ hfr, oM, rfl, by simp only [mRP]; unfold oM frameBytes; omega⟩
    · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega⟩
  exact ⟨cr, cw⟩

/-- The call of `vg_rsa_public_precomputed_checked`: `M^e mod n` to `out`,
for whatever modulus `pre`'s first words are of. `M` and the slot of `r₁`
are kept. -/
theorem pdP_call (P : PublicImpl) (name : String)
    {s t : State} (hp : PreFPc s) (he : EnvP s t)
    (hw0 : word t.mem (fbP s) 0 = off (fbP s) oM) (hw1 : word t.mem (fbP s) 8 = s.gpr .rcx)
    (hw2 : word t.mem (fbP s) 16 = stackArg s 12) (hw3 : word t.mem (fbP s) 24 = stackArg s 13)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = stackArg s 14)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call name (P.code)) t fun t' => EnvP s t' ∧
      (∀ nB : List Byte, nB.length = (s.gpr .rcx).toNat →
        Spec.Rsa.publicPrecompute nB =
          some (Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)) →
        Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
          (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat))) ∧
      Spec.Rsa.bytesAt t'.mem (off (fbP s) oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat ∧
      word t'.mem (fbP s) oR1 = word t.mem (fbP s) oR1 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hk2 := hp.k2
  have hsi' := hp.hsi
  obtain ⟨cr, cw⟩ := pdP_covers hp he
  have hv := P.ok
  have hpre := pdP_pre hp he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9
  have hdd : 8 * (P.code).depth + 16 < 2 ^ 64 := by rw [P.depth]; decide
  have hpre' : (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (t.callEntry.withRegions (pdRdP s) (pdWrP s)) := hpre
  have hcov := Covers.append_left cr cw.right
  refine WP.call_mx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := pdRdP s) (wr := pdWrP s)
    hv P.nosp hdd
    hpre' hcov cw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [P.depth, he.rsp] at hf
  have hfE : Frame [stkRP s, outR s, scrR s] s.mem t.callEntry.mem :=
    frameP_call he.mem (callEntryP_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (belowP_sub s)
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by
      unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega)
  have sP := preRP_sub hp
  have hprl := hp.hprl
  have wPre := hp.wPre
  unfold Spec.Rsa.privatePrecomputedWords at hprl
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hcxN, hm₂, hg₂ .rax (by decide), stackArgP_entry he.rsp _ _ (show 0 < 400 by decide),
    Nat.mul_zero, hw0, entryP_bytes he.rsp (show oM + (s.gpr .rcx).toNat ≤ frameBytes by unfold oM frameBytes; omega),
    wordsP_of_frame hfE (hp.dKpre.symm.sub_left sP).symm (hp.dOpre.symm.sub_left sP).symm
      (hp.dpres.sub_left sP).symm (by simp only [preRP] at sP ⊢; omega),
    bytesP_of_frame hfE hp.dKe hp.dOe (hp.des.symm) (by have := hp.wE; omega)] at hpost
  have hapart : ∀ {d n : Nat}, d + n ≤ frameBytes → 32 ≤ d → ∀ r ∈ pdWrP s ++ [below (fbP s) 8],
      (⟨off (fbP s) d, n⟩ : Region).Disjoint r := fun {d n} hdn h32 r hr => by
    simp only [pdWrP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [← hsi']; exact (hp.dKo.sub_left (frameP_sub s hdn))
    · exact hp.dKs.sub_left (frameP_sub s hdn)
    · exact (retP_disjoint s hdn).symm
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frameP_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, ?_, ?_, hcs, hmx⟩
  · simp only [pdWrP, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (by rw [← hsi']; exact sub_refl _))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (belowP_sub s)
  · rw [slotP_keep hf (hapart (by decide) (by decide))]; exact he.sOut
  · rw [slotP_keep hf (hapart (by decide) (by decide))]; exact he.sN
  · rw [slotP_keep hf (hapart (by decide) (by decide))]; exact he.sK
  · rw [slotP_keep hf (hapart (by decide) (by decide))]; exact he.sE
  · rw [slotP_keep hf (hapart (by decide) (by decide))]; exact he.sEl
  · simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hf.bytes (R := ⟨off (fbP s) oM, (s.gpr .rcx).toNat⟩)
      (fun r hr => hapart (by unfold oM frameBytes; omega) (by decide) r hr) (by dsimp only; omega)
      (List.mem_range.mp hi)
  · exact slotP_keep hf (hapart (by decide) (by decide))

end VG.Proof.Rsa.X86_64
