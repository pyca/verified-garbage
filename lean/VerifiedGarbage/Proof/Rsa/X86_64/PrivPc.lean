import VerifiedGarbage.Proof.Rsa.X86_64.PrivCrt

/-!
# `vg_rsa_private_checked` on x86-64: the call of `vg_rsa_public_precompute`

`r₁` kept in its slot, and `n`'s values written to the frame at `oPre`
(`pc_stage`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- A stack argument past a store to the frame. -/
theorem arg_wo {s : State} (m : Mem) {d : Nat} (v : BitVec 64) (hd : d + 8 ≤ frameBytes) {j : Nat} (hj : j < 14) :
    (m.writeW (off (fb s) d) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  rw [stackArgAddr_fb]
  exact word_wo m (fb s) v (by unfold frameBytes at *; omega) (by unfold frameBytes at *; omega)
    (by unfold frameBytes; omega)

/-- `2 ⌈k / 8⌉` from `k`. -/
theorem preWords_val {x : BitVec 64} (hx : x.toNat ≤ 1024) :
    (x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 + (x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 =
      BitVec.ofNat 64 (Spec.Rsa.precomputedWords x.toNat) := by
  rw [sx7]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, show (7 : BitVec 64).toNat = 7 from rfl]
  omega

/-- `r₁` kept, and the arguments of `vg_rsa_public_precompute`. -/
theorem pcArgs_ok {s t : State} (hp : PreF s) (he : Env s t) :
    WP isa (.block pcArgs) t fun t' => Env s t' ∧
      t'.mem = t.mem.writeW (off (fb s) oR1) (t.gpr .rax) ∧ t'.gpr .rdi = off (fb s) oPre ∧
      t'.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .rdx = s.gpr .rdx ∧ t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = stackArg s 12 ∧
      t'.gpr .r9 = stackArg s 13 := by
  have hs := he.scr hp
  have hk2 := hp.k2
  have harg : ∀ j < 14, InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := fun j hj =>
    ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by
      rw [he.rd, hp.hrd]; simp only [List.mem_cons]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))))),
      by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t' =>
      t'.mem = t.mem.writeW (off (fb s) oR1) (t.gpr .rax) ∧ t'.gpr .rdi = off (fb s) oPre ∧
      t'.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
      t'.gpr .rdx = s.gpr .rdx ∧ t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = stackArg s 12 ∧
      t'.gpr .r9 = stackArg s 13) (by
    xrun [pcArgs, lea, preWords, List.cons_append, List.nil_append, ea_sp, he.rsp, arg,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 12) = stackArgAddr s 12 from (stackArgAddr_fb s 12).symm,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 13) = stackArgAddr s 13 from (stackArgAddr_fb s 13).symm,
      hs.st (d := oR1) (by decide), hs.ld (d := oK) (by decide), hs.ld (d := oN) (by decide),
      harg 12 (by decide), harg 13 (by decide), sx_ofNat (show oPre < 2 ^ 31 by decide),
      word_wo t.mem (fb s) (t.gpr .rax) (show oR1 + 8 ≤ oK ∨ oK + 8 ≤ oR1 by decide) (by decide) (by decide),
      word_wo t.mem (fb s) (t.gpr .rax) (show oR1 + 8 ≤ oN ∨ oN + 8 ≤ oR1 by decide) (by decide) (by decide),
      he.sK, he.sN, arg_wo (s := s) t.mem (t.gpr .rax) (show oR1 + 8 ≤ frameBytes by decide) (show 12 < 14 by decide),
      arg_wo (s := s) t.mem (t.gpr .rax) (show oR1 + 8 ≤ frameBytes by decide) (show 13 < 14 by decide),
      he.arg hp (show 12 < 14 by decide), he.arg hp (show 13 < 14 by decide), preWords_val (show
        (s.gpr .rcx).toNat ≤ 1024 by omega)]) rfl) fun t' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ⟨⟨?_, k.2.1.trans he.rd, k.2.2.trans he.wr, ?_,
      ?_, ?_, ?_, ?_, ?_⟩, hm, hdi, hsi, hdx, hcx, h8, h9⟩
  · rw [k.gpr (by decide)]; exact he.rsp
  · rw [hm]
    refine frame_call he.mem (rs := [⟨off (fb s) oR1, 8⟩]) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) fun r hr => ?_
    rw [List.mem_singleton.mp hr]; exact .inl (frame_sub s (by decide))
  all_goals rw [hm, word_wo _ _ _ (by decide) (by decide) (by decide)]
  · exact he.sOut
  · exact he.sN
  · exact he.sK
  · exact he.sE
  · exact he.sEl

/-! ## The call -/

/-- `n`'s values in the frame, `2 ⌈k / 8⌉` words. -/
def preR (s : State) : Region :=
  ⟨off (fb s) oPre, Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8⟩

theorem preWords_le {s : State} (hp : PreF s) : Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ 256 := by
  have := hp.k2; unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega

theorem preR_sub {s : State} (hp : PreF s) : Region.Sub (preR s) (stkR s) :=
  frame_sub s (by have := preWords_le hp; unfold oPre frameBytes; omega)

/-- A region of the frame at `d`, apart from the return address of a call. -/
theorem ret_disjoint (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (below (fb s) 8).Disjoint ⟨off (fb s) d, n⟩ := by
  rw [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl, fb_eq, off_off]
  exact Offset.base_disjoint _ (by omega) (by unfold frameBytes at h; omega)

theorem pc_pre {s t : State} (hp : PreF s) (he : Env s t) (hdi : t.gpr .rdi = off (fb s) oPre)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = stackArg s 12)
    (h9 : t.gpr .r9 = stackArg s 13) :
    pcContract.pre (t.callEntry.withRegions [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [preR s, scrR s]) := by
  have hpw := preWords_le hp
  have hsiN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [pcContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, he.rsp, hsiN, fb_sub8]
  have ⟨hK1, _⟩ := kb_toNat hp
  have e1 : stackBytes = 3248 := rfl
  have e2 : oPre = 1184 := rfl
  have hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_eq s
  have sP := preR_sub hp
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have dRP : (⟨kb s, 8⟩ : Region).Disjoint (preR s) := by
    have := ret_disjoint s (d := oPre) (n := Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8)
      (by unfold oPre frameBytes; omega)
    rwa [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl] at this
  have wP : (off (fb s) oPre).toNat + Spec.Rsa.precomputedWords (s.gpr .rcx).toNat * 8 ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega)]; omega), hfb, ← off, toNat_off (by omega)]; omega
  exact ⟨trivial, rfl, hp.dKn.sub_left sP, hp.dKs.sub_left sP, hp.dns, dRP, hp.dKn.sub_left sR,
    hp.dKs.sub_left sR, wP, hp.wN, hp.wS, ⟨hp.k1, hp.k2⟩, trivial, hp.hsl⟩

/-- The regions `vg_rsa_public_precompute` is given: `n`, and the precomputed
values and the working space. -/
theorem pc_covers {s t : State} (hp : PreF s) (he : Env s t) :
    Covers ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ++ [preR s, scrR s]) (t.rd ++ t.wr) ∧
      Covers [preR s, scrR s] t.wr := by
  have hpw := preWords_le hp
  have hk2 := hp.k2
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [scrR]
  have hn : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region) ∈ t.rd := by rw [he.rd, hp.hrd]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers [preR s, scrR s] t.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oPre, rfl, by simp only [preR]; unfold oPre frameBytes; omega⟩
    · exact ⟨_, hscr, 0, z _, Nat.le_refl _ |>.trans (by simp)⟩
  exact ⟨Covers.append (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hn) cw, cw⟩

/-- The call of `vg_rsa_public_precompute`: `n`'s values in the frame (zeros
if `n` is not valid), and whether it is returned. `M` and `r₁`'s slot are
kept. -/
theorem pc_call (M : Mont) (name : String) (hmx : (Precompute.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Precompute.code M.mm)) (hd : (Precompute.code M.mm).depth = 0) {s t : State} (hp : PreF s)
    (he : Env s t) (hdi : t.gpr .rdi = off (fb s) oPre)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat))
    (hdx : t.gpr .rdx = s.gpr .rdx) (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = stackArg s 12)
    (h9 : t.gpr .r9 = stackArg s 13) :
    WP isa (.call name (Precompute.code M.mm)) t fun t' => Env s t' ∧
      (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
        | some ws => (t'.gpr .rax).setWidth 32 = 1 ∧
          Spec.Rsa.wordsAt t'.mem (off (fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) = ws
        | none => (t'.gpr .rax).setWidth 32 = 0 ∧
          Spec.Rsa.wordsAt t'.mem (off (fb s) oPre) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
            List.replicate (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) 0) ∧
      Spec.Rsa.bytesAt t'.mem (off (fb s) oM) (s.gpr .rcx).toNat =
        Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat ∧
      word t'.mem (fb s) oR1 = word t.mem (fb s) oR1 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hpw := preWords_le hp
  have hk2 := hp.k2
  obtain ⟨hcov, cw⟩ := pc_covers hp he
  refine WP.call_mx (k := pcContract) (pcCode_correct M hmx) hsp (by rw [hd]; decide)
    (pc_pre hp he hdi hsi hdx hcx h8 h9) hcov cw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [hd, he.rsp] at hf
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hpwN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [pcContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, hpwN, hm₂, hg₂ .rax (by decide),
    bytes_of_frame hfE hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega)] at hpost
  have hapart : ∀ {d n : Nat}, d + n ≤ oPre → ∀ r ∈ [preR s, scrR s] ++ [below (fb s) 8],
      (⟨off (fb s) d, n⟩ : Region).Disjoint r := fun {d n} hdn r hr => by
    have := (show oPre = 1184 from rfl)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inl hdn) (by omega) (by unfold oPre at *; omega)
    · exact hp.dKs.sub_left (frame_sub s (by unfold frameBytes; omega))
    · exact (ret_disjoint s (by unfold frameBytes; omega)).symm
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, ?_, ?_, hcs, hmx⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (preR_sub hp)
    · exact .inr (.inr (sub_refl _))
    · exact .inl (below_sub s)
  · rw [slot_keep hf (hapart (by decide))]; exact he.sOut
  · rw [slot_keep hf (hapart (by decide))]; exact he.sN
  · rw [slot_keep hf (hapart (by decide))]; exact he.sK
  · rw [slot_keep hf (hapart (by decide))]; exact he.sE
  · rw [slot_keep hf (hapart (by decide))]; exact he.sEl
  · simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hf.bytes (R := ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩)
      (fun r hr => hapart (by unfold oM oPre; omega) r hr) (by dsimp only; omega) (List.mem_range.mp hi)
  · exact slot_keep hf (hapart (by decide))

end VG.Proof.Rsa.X86_64
