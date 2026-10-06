import VerifiedGarbage.Proof.Rsa.X86_64.PrivPc
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked

/-!
# `vg_rsa_private_checked` on x86-64: the call of `vg_rsa_public_precomputed_checked`

`r₃` kept in its slot, and `M^e mod n` written to `out` (`pd_stage`), for
whatever `M` holds.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem arg_in {s t : State} (hp : PreF s) (he : Env s t) {j : Nat} (hj : j < 14) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by
    rw [he.rd, hp.hrd]; simp only [List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))))),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem word_wo0 (m : Mem) (base : Addr) (v : BitVec 64) {d' : Nat} (h : 8 ≤ d') (hd' : d' + 8 ≤ 4096) :
    (m.writeW base v).readW (off base d') 64 = m.readW (off base d') 64 := by
  have := word_wo m base v (d := 0) (d' := d') (.inl (by omega)) (by decide) hd'
  simpa only [Bignum.word, off, BitVec.add_zero] using this

theorem arg_wo0 {s : State} (m : Mem) (v : BitVec 64) {j : Nat} (hj : j < 14) :
    (m.writeW (fb s) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  have := arg_wo (s := s) m v (d := 0) (by decide) hj
  simpa only [off, BitVec.add_zero] using this

/-- `r₃` kept, and the arguments of `vg_rsa_public_precomputed_checked`. -/
theorem pdArgs_ok {s t : State} (hp : PreF s) (he : Env s t) :
    WP isa (.block pdArgs) t fun t' => Env s t' ∧
      t'.mem = (((((t.mem.writeW (off (fb s) oR3) (t.gpr .rax)).writeW (fb s) (off (fb s) oM)).writeW
        (off (fb s) 8) (s.gpr .rcx)).writeW (off (fb s) 16) (stackArg s 12)).writeW (off (fb s) 24) (stackArg s 13)) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = off (fb s) oPre ∧
      t'.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 := by
  have hs := he.scr hp
  have hk2 := hp.k2
  have h0 : InRegions t.wr (fb s) 8 := by simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t' =>
      t'.mem = (((((t.mem.writeW (off (fb s) oR3) (t.gpr .rax)).writeW (fb s) (off (fb s) oM)).writeW
        (off (fb s) 8) (s.gpr .rcx)).writeW (off (fb s) 16) (stackArg s 12)).writeW (off (fb s) 24) (stackArg s 13)) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = off (fb s) oPre ∧
      t'.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9) (by
    xrun [pdArgs, lea, preWords, List.cons_append, List.nil_append, ea_sp, he.rsp, arg,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 12) = stackArgAddr s 12 from (stackArgAddr_fb s 12).symm,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 13) = stackArgAddr s 13 from (stackArgAddr_fb s 13).symm,
      hs.st (d := oR3) (by decide), h0, hs.st (d := 8) (by decide),
      hs.st (d := 16) (by decide), hs.st (d := 24) (by decide), hs.ld (d := oK) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oE) (by decide), hs.ld (d := oEl) (by decide),
      arg_in hp he (show 12 < 14 by decide), arg_in hp he (show 13 < 14 by decide),
      sx_ofNat (show oPre < 2 ^ 31 by decide), sx_ofNat (show oM < 2 ^ 31 by decide), word_wo, arg_wo, word_wo0, arg_wo0,
      he.sK, he.sOut, he.sE, he.sEl, he.arg hp (show 12 < 14 by decide), he.arg hp (show 13 < 14 by decide),
      preWords_val (show (s.gpr .rcx).toNat ≤ 1024 by omega)]) rfl)
    fun t' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ⟨⟨?_, k.2.1.trans he.rd, k.2.2.trans he.wr, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      hm, hdi, hsi, hdx, hcx, h8, h9⟩
  · rw [k.gpr (by decide)]; exact he.rsp
  · have h0' : (⟨fb s, frameBytes⟩ : Region).Contains (fb s) 8 := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    have fr : ∀ {d : Nat}, d + 8 ≤ frameBytes → (⟨fb s, frameBytes⟩ : Region).Contains (off (fb s) d) 8 :=
      fun hd => Offset.contains_base _ hd (by unfold frameBytes at hd; omega)
    rw [hm]
    refine frame_call he.mem (rs := [⟨fb s, frameBytes⟩]) ?_ fun r hr => ?_
    · exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fr (d := oR3) (by decide))).writeW
        (List.mem_singleton_self _) _ h0').writeW (List.mem_singleton_self _) _ (fr (d := 8) (by decide))).writeW
        (List.mem_singleton_self _) _ (fr (d := 16) (by decide))).writeW (List.mem_singleton_self _) _
        (fr (d := 24) (by decide)))
    · rw [List.mem_singleton.mp hr]
      have := frame_sub s (d := 0) (n := frameBytes) (by decide)
      exact .inl (by simpa only [off, BitVec.add_zero] using this)
  all_goals rw [hm]; simp (disch := decide) only [Bignum.word, word_wo, word_wo0]
  · exact he.sOut
  · exact he.sN
  · exact he.sK
  · exact he.sE
  · exact he.sEl

/-! ## The call -/

/-- `M` in the frame, `k` bytes. -/
def mR (s : State) : Region := ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩

theorem mR_sub {s : State} (hp : PreF s) : Region.Sub (mR s) (stkR s) :=
  frame_sub s (by have := hp.k2; unfold oM frameBytes; omega)

/-- What the call reads: `n`'s values, `e`, `M` and its stack arguments. -/
def pdRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, mR s, ⟨fb s, 32⟩]

/-- What it writes: `out` and the working space. -/
def pdWr (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, scrR s]

theorem word_self0 (m : Mem) (base : Addr) (v : BitVec 64) : word (m.writeW base v) base 0 = v := by
  have := word_writeW_self m base 0 v
  simpa only [off, BitVec.add_zero] using this

theorem pd_pre {s t : State} (hp : PreF s) (he : Env s t)
    (hw0 : word t.mem (fb s) 0 = off (fb s) oM) (hw1 : word t.mem (fb s) 8 = s.gpr .rcx)
    (hw2 : word t.mem (fb s) 16 = stackArg s 12) (hw3 : word t.mem (fb s) 24 = stackArg s 13)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = off (fb s) oPre)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pdContract.pre (t.callEntry.withRegions (pdRd s) (pdWr s)) := by
  have hpw := preWords_le hp
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (pdRd s) (pdWr s)) i = word t.mem (fb s) (8 * i) :=
    fun i hi => stackArg_entry he.rsp _ _ (by omega)
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, hcxN, stackArgAddr_entry he.rsp, hE 0 (by decide), hE 1 (by decide),
    hE 2 (by decide), hE 3 (by decide), Nat.reduceMul, hw0, hw1, hw2, hw3, fb_sub8]
  have ⟨hK1, _⟩ := kb_toNat hp
  have e1 : stackBytes = 3248 := rfl
  have e2 : oPre = 1184 := rfl
  have e3 : oM = 160 := rfl
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_eq s
  have sP := preR_sub hp
  have sM := mR_sub hp
  have sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have rb : below (fb s) 8 = ⟨kb s, 8⟩ := by simp only [below]; rw [← fb_sub8]; rfl
  have dRP : (⟨kb s, 8⟩ : Region).Disjoint (preR s) := by
    rw [← rb]; exact ret_disjoint s (by unfold oPre frameBytes; omega)
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint (mR s) := by
    rw [← rb]; exact ret_disjoint s (by unfold oM frameBytes; omega)
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have dOut : ∀ {r : Region}, Region.Sub r (stkR s) →
      (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint r := fun h => by
    rw [← hsi']; exact (hp.dKo.sub_left h).symm
  have wFr : ∀ {d n : Nat}, d + n ≤ frameBytes → (off (fb s) d).toNat + n ≤ 2 ^ 64 := fun {d n} h => by
    unfold frameBytes at h
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega)]; omega), hfb, ← off, toNat_off (by omega)]; omega
  refine ⟨by omega, rfl, rfl, dOut sP, ?_, dOut sM, ?_, dOut sA, hp.dKs.sub_left sP, hp.des,
    hp.dKs.sub_left sM, (hp.dKs.sub_left sA).symm, ?_, dRP, hp.dKe.sub_left sR, dRM, hp.dKs.sub_left sR, dRA,
    ?_, wFr (by unfold oPre frameBytes; omega), hp.wE, wFr (by unfold oM frameBytes; omega), hp.wS,
    ⟨hp.k1, hp.k2⟩, trivial, trivial, hp.L1, hp.L2, hp.hsl⟩
  · rw [← hsi']; exact hp.dOe
  · rw [← hsi']; exact hp.dOs
  · rw [← hsi']; exact (hp.dKo.sub_left sR)
  · rw [← hsi']; exact hp.wO

/-- Bytes of the frame at `d`, kept by a call's return address. -/
theorem entry_bytes {s t : State} (hsp : t.gpr .rsp = fb s) {d n : Nat} (h : d + n ≤ frameBytes) :
    Spec.Rsa.bytesAt t.callEntry.mem (off (fb s) d) n = Spec.Rsa.bytesAt t.mem (off (fb s) d) n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => (callEntry_frame hsp).bytes (R := ⟨off (fb s) d, n⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (ret_disjoint s h).symm)
    (by dsimp only; unfold frameBytes at h; omega) (List.mem_range.mp hi)

/-- Words of the frame at `d`, kept by a call's return address. -/
theorem entry_words {s t : State} (hsp : t.gpr .rsp = fb s) {d n : Nat} (h : d + 8 * n ≤ frameBytes) :
    Spec.Rsa.wordsAt t.callEntry.mem (off (fb s) d) n = Spec.Rsa.wordsAt t.mem (off (fb s) d) n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  show t.callEntry.mem.readW (off (off (fb s) d) (8 * i)) 64 = t.mem.readW (off (off (fb s) d) (8 * i)) 64
  rw [off_off]
  exact (callEntry_frame hsp).readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (ret_disjoint s (by unfold frameBytes at *; omega)).symm) (by decide)

/-- The regions `vg_rsa_public_precomputed_checked` is given. -/
theorem pd_covers {s t : State} (hp : PreF s) (he : Env s t) :
    Covers (pdRd s) (t.rd ++ t.wr) ∧ Covers (pdWr s) t.wr := by
  have hpw := preWords_le hp
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pdWr s) t.wr := Covers.of_mem fun r hr => by
    simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [he.wr, hp.hwr]
    rcases hr with rfl | rfl
    · rw [← hsi']; simp
    · simp [scrR]
  have cr : Covers (pdRd s) (t.rd ++ t.wr) := Covers.of_sub fun r hr => by
    simp only [pdRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hfr, oPre, rfl, by simp only [preR]; unfold oPre frameBytes; omega⟩
    · exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, List.mem_append_left _ (by rw [he.rd, hp.hrd]; simp), 0, z _,
        by dsimp only; omega⟩
    · exact ⟨_, List.mem_append_right _ hfr, oM, rfl, by simp only [mR]; unfold oM frameBytes; omega⟩
    · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega⟩
  exact ⟨cr, cw⟩

/-- The call of `vg_rsa_public_precomputed_checked`: `M^e mod n` to `out`,
for whatever modulus `n`'s values in the frame are of. `M` and the slots of
`r₁` and `r₃` are kept. -/
theorem pd_call (M : Mont) (name : String) (hmx : (Precomputed.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Checked.precomputedChecked M.mm)) (hd : (Checked.precomputedChecked M.mm).depth = 0)
    {s t : State} (hp : PreF s) (he : Env s t)
    (hw0 : word t.mem (fb s) 0 = off (fb s) oM) (hw1 : word t.mem (fb s) 8 = s.gpr .rcx)
    (hw2 : word t.mem (fb s) 16 = stackArg s 12) (hw3 : word t.mem (fb s) 24 = stackArg s 13)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = off (fb s) oPre)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call name (Checked.precomputedChecked M.mm)) t fun t' => Env s t' ∧
      (∀ nB : List Byte, nB.length = (s.gpr .rcx).toNat →
        Spec.Rsa.publicPrecompute nB =
          some (Spec.Rsa.wordsAt t.mem (off (fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)) →
        Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
          (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
            (Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat))) ∧
      Spec.Rsa.bytesAt t'.mem (off (fb s) oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat ∧
      word t'.mem (fb s) oR1 = word t.mem (fb s) oR1 ∧ word t'.mem (fb s) oR3 = word t.mem (fb s) oR3 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hpw := preWords_le hp
  have hk2 := hp.k2
  have hsi' := hp.hsi
  obtain ⟨cr, cw⟩ := pd_covers hp he
  have hv := Proof.Rsa.X86_64.precomputedChecked_correct M hmx
  have hpre := pd_pre hp he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9
  have hdd : 8 * (Checked.precomputedChecked M.mm).depth + 16 < 2 ^ 64 := by rw [hd]; decide
  have hpre' : (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (t.callEntry.withRegions (pdRd s) (pdWr s)) := hpre
  have hcov := Covers.append_left cr cw.right
  refine WP.call_mx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := pdRd s) (wr := pdWr s)
    hv hsp hdd
    hpre' hcov cw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [hd, he.rsp] at hf
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hcxN, hm₂, hg₂ .rax (by decide), stackArg_entry he.rsp _ _ (show 0 < 400 by decide),
    Nat.mul_zero, hw0, entry_bytes he.rsp (show oM + (s.gpr .rcx).toNat ≤ frameBytes by unfold oM frameBytes; omega),
    entry_words he.rsp (show oPre + 8 * Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ frameBytes by
      unfold oPre frameBytes; omega),
    bytes_of_frame hfE hp.dKe hp.dOe (hp.des.symm) (by have := hp.wE; omega)] at hpost
  have hapart : ∀ {d n : Nat}, d + n ≤ frameBytes → 32 ≤ d → ∀ r ∈ pdWr s ++ [below (fb s) 8],
      (⟨off (fb s) d, n⟩ : Region).Disjoint r := fun {d n} hdn h32 r hr => by
    simp only [pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [← hsi']; exact (hp.dKo.sub_left (frame_sub s hdn))
    · exact hp.dKs.sub_left (frame_sub s hdn)
    · exact (ret_disjoint s hdn).symm
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, ?_, ?_, ?_, hcs, hmx⟩
  · simp only [pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (by rw [← hsi']; exact sub_refl _))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (below_sub s)
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sOut
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sN
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sK
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sE
  · rw [slot_keep hf (hapart (by decide) (by decide))]; exact he.sEl
  · simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hf.bytes (R := ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩)
      (fun r hr => hapart (by unfold oM frameBytes; omega) (by decide) r hr) (by dsimp only; omega)
      (List.mem_range.mp hi)
  · exact slot_keep hf (hapart (by decide) (by decide))
  · exact slot_keep hf (hapart (by decide) (by decide))

end VG.Proof.Rsa.X86_64
