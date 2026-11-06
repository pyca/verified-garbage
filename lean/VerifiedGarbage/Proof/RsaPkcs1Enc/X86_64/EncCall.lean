module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncPre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the call of `vg_rsa_public_checked`

The call's arguments from the slots (`callArgs_run`), what the callee reads
and writes (`pubRd`, `pubWr`), and what holds after the call (`AfterCall`,
`PostCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## The arguments -/

theorem callArgs_run {s t : State} (hp : EPre s) (h : PreCall s t) :
    WP isa (.block callArgs) t fun t' => t'.mem = t.mem ∧ t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧
      t'.gpr .rdx = s.gpr .rdx ∧ t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] t t' := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega_arith)
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (c := .block callArgs) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rcx ∧ t'.gpr .rdx = s.gpr .rdx ∧
      t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, k⟩
  xrun [callArgs, ea_sp, h.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide),
    hs.ld (d := oN) (by decide), hs.ld (d := oE) (by decide), hs.ld (d := oEl) (by decide), h.slots.sOut,
    h.slots.sK, h.slots.sN, h.slots.sE, h.slots.sEl]
  done

/-! ## The callee's view -/

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 encStack

theorem fb_sub8 (s : State) : fb s - 8 = kb s := by
  rw [fb_eq]; exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : EPre s) : (kb s).toNat + encStack + 56 ≤ 2 ^ 64 ∧
    (kb s).toNat + encStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack frameBytes at *; omega_arith

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

/-- What `vg_rsa_public_checked` reads: `n`, `e`, `EM` and its stack
arguments. -/
def pubRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩, ⟨fb s, 32⟩]

/-- What it writes: `out` and the working space. -/
def pubWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩]

theorem pub_covers {s t : State} (hp : EPre s) (h : PreCall s t) :
    Covers (pubRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  have hk2 := hp.k2
  have hsi := hp.hsi
  have e2 : oEM = 80 := rfl
  have e3 : frameBytes = 1112 := rfl
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  have hscr : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr]; simp
  have hout : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pubWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by dsimp only; omega_arith⟩
    · exact ⟨_, hscr, 0, z _, by dsimp only; omega_arith⟩
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  have cr : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArgAddr s 0, 48⟩]
      (t.rd ++ t.wr) := by rw [h.rd]; exact hp.hrd.left
  apply Covers.of_forall
  intro r hr
  simp only [pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_append_right _ hfr, oEM, rfl, by dsimp only; omega_arith⟩
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega_arith⟩

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

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A buffer of the caller that the function does not write, from memory
changed only where it may write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- The modulus and the exponent of an entry state. -/
abbrev nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
abbrev eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat

/-- After the call, whatever it wrote to `out`: the frame and its slots. -/
structure AfterCall (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  slots : Slots s t.mem
  sZ : word t.mem (fb s) oZ = zmask (psB s)

/-- After the call. -/
structure PostCall (s t : State) : Prop extends AfterCall s t where
  res : Spec.Rsa.written t.mem (s.gpr .rdi) (kOf s) ((t.gpr .rax).setWidth 32)
    (Spec.Rsa.publicOpChecked (nB s) (eB s) (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)))

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem below_eq (s : State) : below (fb s) 8 = ⟨kb s, 8⟩ := by
  simp only [below]; rw [← fb_sub8]; rfl

/-- Words of the frame below `EM` are apart from what the call writes. -/
theorem slot_apart {s : State} (hp : EPre s) {d n : Nat} (hd : d + n ≤ frameBytes) :
    ∀ r ∈ pubWr s ++ [below (fb s) 8], (⟨off (fb s) d, n⟩ : Region).Disjoint r := by
  have ⟨hK1, _⟩ := kb_toNat hp
  have e1 : encStack = 1120 := rfl
  have e3 : frameBytes = 1112 := rfl
  have hsi := hp.hsi
  intro r hr
  simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := hp.dKo; rw [hsi] at this; exact this.sub_left (frame_sub s hd)
  · exact hp.dKs.sub_left (frame_sub s hd)
  · rw [below_eq, fb_eq, off_off]
    exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

end VG.Proof.RsaPkcs1Enc.X86_64
