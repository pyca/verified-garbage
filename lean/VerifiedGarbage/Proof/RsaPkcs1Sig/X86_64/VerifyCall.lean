import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyFrame

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the call of `vg_rsa_public_checked`

The arguments kept in the frame's slots and those of the call
(`pubArgs_ok`), and the call (`pub_call`): it runs from the frame with its
stack arguments at `rsp`, writing `s^e mod n` to `EM₁`, and returns with the
slots kept.

The callee is any code meeting `pubChk`, the contract of
`vg_rsa_public_checked` on the registers: `vg_rsa_public`'s, with BoringSSL's
limits on `e` (`Spec.Rsa.publicOpChecked`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- The postcondition of `vg_rsa_public_checked` on the registers. -/
def pubChkPost (s s' : State) : Prop :=
  Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))

/-- `vg_rsa_public_checked` on the registers: `vg_rsa_public`'s contract,
with BoringSSL's limits on `e`. -/
def pubChk : Contract isa where
  pre := pubContract.pre
  pub := pubContract.pub
  post := pubChkPost

/-- An implementation of `vg_rsa_public_checked`, and what its callers need
of it. -/
structure PubImpl where
  name : String
  code : Prog isa
  ok : ∀ s, pubChk.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pubChk.post s s'
  ct : ConstantTime isa pubChk.pre pubChk.pub code
  nosp : NoSp code
  depth : code.depth = 0
  spSafe : code.all (fun i => !isa.writesSp i) = true

end VG.Proof.RsaPkcs1Sig.X86_64

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## The arguments -/

def slotStores : List Instr :=
  [.store (sp oN) .rdi, .store (sp oK) .rsi, .store (sp oE) .rdx, .store (sp oEl) .rcx,
    .store (sp oH) .r8, .store (sp oD) .r9]

def callArgs : List Instr :=
  [.mov .rax (.mem (arg 1)), .mov .r10 (.mem (arg 3)), .mov .r11 (.mem (arg 4)),
    .store (sp 0) .rax, .store (sp 8) .rsi, .store (sp 16) .r10, .store (sp 24) .r11,
    .mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx), .mov .rdx (.reg .rdi), .mov .rcx (.reg .rsi)] ++
  lea .rdi oEM1

theorem pubArgs_eq : pubArgs = slotStores ++ callArgs := rfl

/-- The frame's push and the slots. -/
theorem slotStores_ok {s A : State} (hp : PreV s) (hA : Keep [.rax] (allocState frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block slotStores) A fun t =>
      Keep [.rax] (allocState frameBytes s) t ∧ Outside (fb s) 0 frameBytes s.mem t.mem ∧
      word t.mem (fb s) oN = s.gpr .rdi ∧ word t.mem (fb s) oK = s.gpr .rsi ∧
      word t.mem (fb s) oE = s.gpr .rdx ∧ word t.mem (fb s) oEl = s.gpr .rcx ∧
      word t.mem (fb s) oH = s.gpr .r8 ∧ word t.mem (fb s) oD = s.gpr .r9 := by
  have hF := fb_toNat hp
  have hsp : A.gpr .rsp = fb s := hA.gpr (by decide)
  have hs : Scr A (fb s) frameBytes := Scr.of_mem (by rw [hA.2.2]; exact List.mem_cons_self ..) (by omega)
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → A.gpr r = s.gpr r := fun r h h' => by
    rw [hA.gpr (by simpa using h')]; simp [allocState_gpr, h]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (off (fb s) oN) (s.gpr .rdi)).writeW (off (fb s) oK) (s.gpr .rsi)).writeW
        (off (fb s) oE) (s.gpr .rdx)).writeW (off (fb s) oEl) (s.gpr .rcx)).writeW (off (fb s) oH)
        (s.gpr .r8)).writeW (off (fb s) oD) (s.gpr .r9)) (by
    xrun [slotStores, ea_sp, hsp, hs.st (d := oN) (by decide), hs.st (d := oK) (by decide),
      hs.st (d := oE) (by decide), hs.st (d := oEl) (by decide), hs.st (d := oH) (by decide),
      hs.st (d := oD) (by decide), hAm, g .rdi (by decide) (by decide), g .rsi (by decide) (by decide),
      g .rdx (by decide) (by decide), g .rcx (by decide) (by decide), g .r8 (by decide) (by decide),
      g .r9 (by decide) (by decide)]) rfl) fun t ⟨hm, k⟩ => ⟨(hA.trans k).mono (by simp), ?_, ?_⟩
  · rw [hm]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega
    unfold frameBytes at hx hx'
    simp only [oN, oK, oE, oEl, oH, oD] at *
    rw [writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega)]
  · rw [hm]
    simp (disch := decide) only [word_wo, word_writeW_self, oN, oK, oE, oEl, oH, oD, and_self]

/-- The arguments of `vg_rsa_public_checked`. -/
theorem callArgs_ok {s t : State} (hp : PreV s) (hk : Keep [.rax] (allocState frameBytes s) t)
    (ho : Outside (fb s) 0 frameBytes s.mem t.mem) :
    WP isa (.block callArgs) t fun t' => Keep [.rax, .rdi, .rdx, .rcx, .r8, .r9, .r10, .r11] t t' ∧
      t'.mem = (((t.mem.writeW (fb s) (stackArg s 1)).writeW (off (fb s) 8) (s.gpr .rsi)).writeW
        (off (fb s) 16) (stackArg s 3)).writeW (off (fb s) 24) (stackArg s 4) ∧
      t'.gpr .rdi = off (fb s) oEM1 ∧ t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rdi ∧
      t'.gpr .rcx = s.gpr .rsi ∧ t'.gpr .r8 = s.gpr .rdx ∧ t'.gpr .r9 = s.gpr .rcx := by
  have hF := fb_toNat hp
  have hsp : t.gpr .rsp = fb s := hk.gpr (by decide)
  have hs : Scr t (fb s) frameBytes :=
    Scr.of_mem (by rw [hk.2.2]; exact List.mem_cons_self ..) (by omega)
  have hrd : t.rd = s.rd := hk.2.1
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → t.gpr r = s.gpr r := fun r h h' => by
    rw [hk.gpr (by simpa using h')]; simp [allocState_gpr, h]
  have h0 : InRegions t.wr (fb s) 8 := by
    simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.keep [.rax, .rdi, .rdx, .rcx, .r8, .r9, .r10, .r11] (by
    have h8 : InRegions t.wr (fb s + 8) 8 := hs.st (d := 8) (by decide)
    have h16 : InRegions t.wr (fb s + 16) 8 := hs.st (d := 16) (by decide)
    have h24 : InRegions t.wr (fb s + 24) 8 := hs.st (d := 24) (by decide)
    xrun [callArgs, lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, hsp, h0, h8, h16, h24,
      arg_in hp hrd (show 1 < 5 by decide), arg_in hp hrd (show 3 < 5 by decide),
      arg_in hp hrd (show 4 < 5 by decide), arg_outside hp ho (show 1 < 5 by decide),
      arg_outside hp ho (show 3 < 5 by decide), arg_outside hp ho (show 4 < 5 by decide),
      hs.st (d := 8) (by decide), hs.st (d := 16) (by decide), hs.st (d := 24) (by decide),
      sx_ofNat (show oEM1 < 2 ^ 31 by decide),
      g .rsi (by decide) (by decide), g .rdx (by decide) (by decide), g .rcx (by decide) (by decide),
      g .rdi (by decide) (by decide)]) rfl |> fun h => WP.mono h fun t' ⟨q, k⟩ => ⟨k, q⟩

/-! ## The call -/

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (kb s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
  rw [show kb s + BitVec.ofNat 64 0 = kb s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_eq, off_off, show 8 + 8 * i = 8 * (i + 1) by omega]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_eq]

/-- `EM₁` in the frame. -/
def em1R (s : State) : Region := ⟨off (fb s) oEM1, (s.gpr .rsi).toNat⟩

/-- What the call reads: `n`, `e`, `sig` and its stack arguments. -/
def pubRd (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨stackArg s 1, (s.gpr .rsi).toNat⟩,
    ⟨fb s, 32⟩]

/-- What it writes: `EM₁` and the working space. -/
def pubWr (s : State) : List Region := [em1R s, scrR s]

theorem pub_pre {s t : State} (hp : PreV s) (hsig : stackArg s 2 = s.gpr .rsi) (hsp : t.gpr .rsp = fb s)
    (hw0 : word t.mem (fb s) 0 = stackArg s 1) (hw1 : word t.mem (fb s) 8 = s.gpr .rsi)
    (hw2 : word t.mem (fb s) 16 = stackArg s 3) (hw3 : word t.mem (fb s) 24 = stackArg s 4)
    (hdi : t.gpr .rdi = off (fb s) oEM1) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdi)
    (hcx : t.gpr .rcx = s.gpr .rsi) (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    pubChk.pre (t.callEntry.withRegions (pubRd s) (pubWr s)) := by
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) i = word t.mem (fb s) (8 * i) :=
    fun i hi => stackArg_entry hsp _ _ (by omega)
  simp only [pubChk, pubContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide),
    Nat.reduceMul, hw0, hw1, hw2, hw3, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp
  have e1 : verStack = 2144 := rfl
  have e2 : oEM1 = 80 := rfl
  have e3 : frameBytes = 2136 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have sM : Region.Sub (em1R s) (stkR s) := frame_sub s (by unfold oEM1 frameBytes; omega)
  have sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_eq s
  have dMA : (em1R s).Disjoint ⟨fb s, 32⟩ := Offset.disjoint_base _ (by decide) (by omega)
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint (em1R s) := by
    simp only [em1R]; rw [hfb, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (off (fb s) oEM1).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega)]; unfold oEM1; omega), hfb, ← off,
      toNat_off (by omega)]; unfold oEM1; omega
  have dKg : (stkR s).Disjoint ⟨stackArg s 1, (s.gpr .rsi).toNat⟩ := by rw [← hsig]; exact hp.dKg
  have dgs : (⟨stackArg s 1, (s.gpr .rsi).toNat⟩ : Region).Disjoint (scrR s) := by rw [← hsig]; exact hp.dgs
  have wG : (stackArg s 1).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := by rw [← hsig]; exact hp.wG
  refine ⟨by omega, rfl, rfl, hp.dKn.sub_left sM, hp.dKe.sub_left sM, dKg.sub_left sM, hp.dKs.sub_left sM, dMA,
    hp.dns, hp.des, dgs, (hp.dKs.sub_left sA).symm, dRM, hp.dKn.sub_left sR, hp.dKe.sub_left sR,
    dKg.sub_left sR, hp.dKs.sub_left sR, dRA, wM, hp.wN, hp.wE, wG, hp.wS, ⟨hk1, hk2⟩, trivial, trivial, hp.L1,
    hp.L2, hp.hsl⟩

/-! ## Memory across the call -/

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- Memory changed by a call from the frame, within regions in the stack
the function uses or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {s : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨off (fb s) d, 8⟩ : Region).Disjoint r) : word m' (fb s) d = word m (fb s) d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The slots are apart from `EM₁`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : PreV s) {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ oEM1) :
    ∀ r ∈ pubWr s ++ [below (fb s) 8], (⟨off (fb s) d, 8⟩ : Region).Disjoint r := by
  have hk2 := hp.k2
  intro r hr
  simp only [pubWr, em1R, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by unfold oEM1 at *; omega) (by unfold oEM1 at *; omega)
  · exact (hp.dKs.sub_left (frame_sub s (by unfold oEM1 frameBytes at *; omega)))
  · exact (ret_disjoint s (by unfold oEM1 frameBytes at *; omega)).symm

theorem pub_covers {s t : State} (hp : PreV s) (hsig : stackArg s 2 = s.gpr .rsi) (he : Env s t) :
    Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  have hk2 := hp.k2
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [scrR]
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pubWr, em1R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oEM1, rfl, by dsimp only; unfold oEM1 frameBytes; omega⟩
    · exact ⟨_, hscr, 0, z _, by simp only [scrR]; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
  simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 1, (stackArg s 2).toNat⟩ (by rw [hp.hrd]; simp), 0, z _,
      by dsimp only; rw [hsig]; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega⟩

/-- The call of `vg_rsa_public_checked`: `EM₁` holds `s^e mod n`, which it
returns, or zeros. -/
theorem pub_call (v : PubImpl) {s t : State} (hp : PreV s) (hsig : stackArg s 2 = s.gpr .rsi) (he : Env s t)
    (hw0 : word t.mem (fb s) 0 = stackArg s 1) (hw1 : word t.mem (fb s) 8 = s.gpr .rsi)
    (hw2 : word t.mem (fb s) 16 = stackArg s 3) (hw3 : word t.mem (fb s) 24 = stackArg s 4)
    (hdi : t.gpr .rdi = off (fb s) oEM1) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdi)
    (hcx : t.gpr .rcx = s.gpr .rsi) (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.name v.code) t fun t' => Env s t' ∧
      Spec.Rsa.written t'.mem (off (fb s) oEM1) (s.gpr .rsi).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat)) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := pub_covers hp hsig he
  refine WP.call_mx (k := pubChk) v.ok v.nosp (by rw [v.depth]; decide)
    (pub_pre hp hsig he.rsp hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, he.rsp] at hf
  have hE : stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = stackArg s 1 :=
    (stackArg_entry he.rsp _ _ (by omega)).trans hw0
  have hfE : Frame [stkR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hk2 := hp.k2
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk hs hl =>
    bytes_of_frame hfE hk hs hl
  simp only [pubChk, pubChkPost, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, h9, hE, hm₂, hg₂ .rax (by decide)] at hpost
  rw [b hp.dKn hp.dns.symm (by have := hp.wN; omega), b hp.dKe hp.des.symm (by have := hp.wE; omega),
    b (by rw [← hsig]; exact hp.dKg) (by rw [← hsig]; exact hp.dgs.symm) (by omega)] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, hcs, hmx⟩
  · simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (frame_sub s (by unfold oEM1 frameBytes; omega))
    · exact .inr (sub_refl _)
    · exact .inl (below_sub s)
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sN
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sK
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sE
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sEl
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sH
  · rw [slot_keep hf (slot_apart hp (by decide) (by decide))]; exact he.sD

end VG.Proof.RsaPkcs1Sig.X86_64.Ver
