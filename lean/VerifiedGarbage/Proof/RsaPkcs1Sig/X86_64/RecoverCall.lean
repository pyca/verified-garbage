module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverFrame
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pkcs1_recover` on x86-64: the call of `vg_rsa_public_checked`

As for `vg_rsa_pkcs1_verify` (`VerifyCall.lean`): the arguments kept in the
frame's slots and those of the call (`slotStores_ok`, `callArgs_ok`), and
what the call reads and writes (`pubRd`, `pubWr`, `pub_covers`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq fb_sub8 toNat_off frame_sub below_sub
  ret_disjoint outside_frame stackArgAddr_fb stackArgAddr_eq ea_sp word_wo allocState_gpr arg_ea
  stackArg_entry stackArgAddr_entry callEntry_frame sub_refl slot_keep)

/-! ## The arguments -/

def slotStores : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oOl) .rsi, .store (sp oN) .rdx, .store (sp oK) .rcx,
    .store (sp oE) .r8, .store (sp oEl) .r9]

def callArgs : List Instr :=
  [.mov .rax (.mem (arg 1)), .mov .r10 (.mem (arg 3)), .mov .r11 (.mem (arg 4)),
    .store (sp 0) .rax, .store (sp 8) .rcx, .store (sp 16) .r10, .store (sp 24) .r11,
    .mov .rsi (.reg .rcx)] ++
  lea .rdi oEM1

theorem pubArgs_eq : pubArgs = slotStores ++ callArgs := rfl

/-- The slots. -/
theorem slotStores_ok {s A : State} (hp : PreR s) (hA : Keep [.rax] (allocState frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block slotStores) A fun t =>
      Keep [.rax] (allocState frameBytes s) t ∧ Outside (fb s) 0 frameBytes s.mem t.mem ∧
      word t.mem (fb s) oOut = s.gpr .rdi ∧ word t.mem (fb s) oOl = s.gpr .rsi ∧
      word t.mem (fb s) oN = s.gpr .rdx ∧ word t.mem (fb s) oK = s.gpr .rcx ∧
      word t.mem (fb s) oE = s.gpr .r8 ∧ word t.mem (fb s) oEl = s.gpr .r9 := by
  have hF := fb_toNat hp
  have hsp : A.gpr .rsp = fb s := hA.gpr (by decide)
  have hs : Scr A (fb s) frameBytes := Scr.of_mem (by rw [hA.2.2]; exact List.mem_cons_self ..) (by omega_arith)
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → A.gpr r = s.gpr r := fun r h h' => by
    rw [hA.gpr (by simpa using h')]; simp [allocState_gpr, h]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (off (fb s) oOut) (s.gpr .rdi)).writeW (off (fb s) oOl) (s.gpr .rsi)).writeW
        (off (fb s) oN) (s.gpr .rdx)).writeW (off (fb s) oK) (s.gpr .rcx)).writeW (off (fb s) oE)
        (s.gpr .r8)).writeW (off (fb s) oEl) (s.gpr .r9)) (by
    xrun [slotStores, ea_sp, hsp, hs.st (d := oOut) (by decide), hs.st (d := oOl) (by decide),
      hs.st (d := oN) (by decide), hs.st (d := oK) (by decide), hs.st (d := oE) (by decide),
      hs.st (d := oEl) (by decide), hAm, g .rdi (by decide) (by decide), g .rsi (by decide) (by decide),
      g .rdx (by decide) (by decide), g .rcx (by decide) (by decide), g .r8 (by decide) (by decide),
      g .r9 (by decide) (by decide)]) rfl) fun t ⟨hm, k⟩ => ⟨(hA.trans k).mono (by simp), ?_, ?_⟩
  · rw [hm]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega_arith
    unfold frameBytes at hx hx'
    simp only [oOut, oOl, oN, oK, oE, oEl] at *
    rw [writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]
  · rw [hm]
    simp (disch := decide) only [word_wo, word_writeW_self, oOut, oOl, oN, oK, oE, oEl, and_self]

/-- The arguments of `vg_rsa_public_checked`. -/
theorem callArgs_ok {s t : State} (hp : PreR s) (hk : Keep [.rax] (allocState frameBytes s) t)
    (ho : Outside (fb s) 0 frameBytes s.mem t.mem) :
    WP isa (.block callArgs) t fun t' => Keep [.rax, .rdi, .rsi, .r10, .r11] t t' ∧
      t'.mem = (((t.mem.writeW (fb s) (stackArg s 1)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW
        (off (fb s) 16) (stackArg s 3)).writeW (off (fb s) 24) (stackArg s 4) ∧
      t'.gpr .rdi = off (fb s) oEM1 ∧ t'.gpr .rsi = s.gpr .rcx := by
  have hF := fb_toNat hp
  have hsp : t.gpr .rsp = fb s := hk.gpr (by decide)
  have hs : Scr t (fb s) frameBytes :=
    Scr.of_mem (by rw [hk.2.2]; exact List.mem_cons_self ..) (by omega_arith)
  have hrd : t.rd = s.rd := hk.2.1
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → t.gpr r = s.gpr r := fun r h h' => by
    rw [hk.gpr (by simpa using h')]; simp [allocState_gpr, h]
  have h0 : InRegions t.wr (fb s) 8 := by
    simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.keep [.rax, .rdi, .rsi, .r10, .r11] (by
    have h8 : InRegions t.wr (fb s + 8) 8 := hs.st (d := 8) (by decide)
    have h16 : InRegions t.wr (fb s + 16) 8 := hs.st (d := 16) (by decide)
    have h24 : InRegions t.wr (fb s + 24) 8 := hs.st (d := 24) (by decide)
    xrun [callArgs, lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, hsp, h0, h8, h16, h24,
      hs.st (d := 8) (by decide), hs.st (d := 16) (by decide), hs.st (d := 24) (by decide),
      arg_in hp hrd (show 1 < 5 by decide), arg_in hp hrd (show 3 < 5 by decide),
      arg_in hp hrd (show 4 < 5 by decide), arg_outside hp ho (show 1 < 5 by decide),
      arg_outside hp ho (show 3 < 5 by decide), arg_outside hp ho (show 4 < 5 by decide),
      sx_ofNat (show oEM1 < 2 ^ 31 by decide), g .rcx (by decide) (by decide)]) rfl |>
    fun h => WP.mono h fun t' ⟨q, k⟩ => ⟨k, q⟩

/-! ## The call -/

/-- `EM₁` in the frame. -/
def em1R (s : State) : Region := ⟨off (fb s) oEM1, (s.gpr .rcx).toNat⟩

/-- What the call reads: `n`, `e`, `sig` and its stack arguments. -/
def pubRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, (s.gpr .rcx).toNat⟩,
    ⟨fb s, 32⟩]

/-- What it writes: `EM₁` and the working space. -/
def pubWr (s : State) : List Region := [em1R s, scrR s]

/-! ## Memory across the call -/

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkR s, outR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkR s) ∨ Region.Sub r (outR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkR s, outR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

/-- The slots are apart from `EM₁`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : PreR s) {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ oEM1) :
    ∀ r ∈ pubWr s ++ [below (fb s) 8], (⟨off (fb s) d, 8⟩ : Region).Disjoint r := by
  have hk2 := hp.k2
  intro r hr
  simp only [pubWr, em1R, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by unfold oEM1 at *; omega_arith) (by unfold oEM1 at *; omega_arith)
  · exact (hp.dKs.sub_left (frame_sub s (by unfold oEM1 frameBytes at *; omega_arith)))
  · exact (ret_disjoint s (by unfold oEM1 frameBytes at *; omega_arith)).symm

theorem pub_covers {s t : State} (hp : PreR s) (hsig : stackArg s 2 = s.gpr .rcx) (he : Env s t) :
    Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  have hk2 := hp.k2
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [scrR]
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pubWr, em1R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oEM1, rfl, by dsimp only; unfold oEM1 frameBytes; omega_arith⟩
    · exact ⟨_, hscr, 0, z _, by simp only [scrR]; omega_arith⟩
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  have cr : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩] (t.rd ++ t.wr) := by
    rw [he.rd]; exact hp.hrd.left
  apply Covers.of_forall
  intro r hr
  simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · rw [← hsig]
    exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega_arith⟩

end VG.Proof.RsaPkcs1Sig.X86_64.Rec
