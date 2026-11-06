module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the call of `vg_rsa_public_checked`

The arguments kept in the frame's slots and those of the call
(`slotStores_ok`, `callArgs_ok`), what the call writes (`pubWr`), and the
slots it keeps (`slot_keep`, `slot_apart`).

The callee is any code meeting `pubChk`, the contract of
`vg_rsa_public_checked` on the registers: `vg_rsa_public`'s, with BoringSSL's
limits on `e` (`Spec.Rsa.publicOpChecked`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

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
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## The arguments -/

def slotStores : List Instr :=
  [.store (sp oN) .rdi, .store (sp oK) .rsi, .store (sp oE) .rdx, .store (sp oEl) .rcx,
    .store (sp oH) .r8, .store (sp oD) .r9]

def callArgs : List Instr :=
  ([.mov .rax (.mem (arg 1)), .mov .r10 (.mem (arg 3)), .mov .r11 (.mem (arg 4)),
    .store (sp 0) .rax, .store (sp 8) .rsi, .store (sp 16) .r10, .store (sp 24) .r11,
    .mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx), .mov .rdx (.reg .rdi), .mov .rcx (.reg .rsi)] : List Instr) ++
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
  have hs : Scr A (fb s) frameBytes := Scr.of_mem (by rw [hA.2.2]; exact List.mem_cons_self ..) (by omega_arith)
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
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega_arith
    unfold frameBytes at hx hx'
    simp only [oN, oK, oE, oEl, oH, oD] at *
    rw [writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]
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
    Scr.of_mem (by rw [hk.2.2]; exact List.mem_cons_self ..) (by omega_arith)
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
  have hsep := Offset.sep (kb s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith)
  rw [show kb s + BitVec.ofNat 64 0 = kb s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_eq, off_off, show 8 + 8 * i = 8 * (i + 1) by omega_arith]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_eq]

/-- `EM₁` in the frame. -/
def em1R (s : State) : Region := ⟨off (fb s) oEM1, (s.gpr .rsi).toNat⟩

/-- What the call writes: `EM₁` and the working space. -/
def pubWr (s : State) : List Region := [em1R s, scrR s]

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
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by unfold oEM1 at *; omega_arith) (by unfold oEM1 at *; omega_arith)
  · exact (hp.dKs.sub_left (frame_sub s (by unfold oEM1 frameBytes at *; omega_arith)))
  · exact (ret_disjoint s (by unfold oEM1 frameBytes at *; omega_arith)).symm

end VG.Proof.RsaPkcs1Sig.X86_64.Ver
