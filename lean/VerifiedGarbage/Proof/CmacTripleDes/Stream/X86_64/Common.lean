module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Finalize
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Impl.CmacTripleDes.X86_64
public import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Update
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Init
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.CmacTripleDes.Scratch
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! ### `CmacTripleDes.Stream.X86_64.Inline`, which this module and modules that import it used -/

section

/-! ### `CmacTripleDes.X86_64.Verified`, which only this module used -/

section

/-! ### `CmacTripleDes.X86_64.FinalizeCorrect`, which only this module used -/

section

/-!
# TDEA-CMAC on x86-64: `vg_cmac_triple_des_finalize` is correct

After the branch on the length, `rax` holds `Mₙ` (`BPost`); the function XORs
in the chaining value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as the
state, the MAC (`macFull_split8`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacTripleDes.X86_64 VG.Proof.CmacTripleDes VG.Proof.Cmac

/-- What the first block leaves. -/
structure P1 (s₀ : State) (W St P S : Addr) (s : State) : Prop where
  r15 : s.gpr .r15 = S
  r14 : s.gpr .r14 = W
  rbp : s.gpr .rbp = St
  rdi : s.gpr .rdi = W
  rdx : s.gpr .rdx = P
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  mem : s.mem = savedMem s₀ S
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {s₀ : State} {W St P S : Addr} {L : Nat} (hp : FPre s₀ W St P S L)
include hp

theorem FPre.save_frame : ∀ r ∈ [(⟨S + BitVec.ofNat 64 48, 48⟩ : Region)], (⟨P, L⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hp.last_scr.sub_right (FPre.scrD (by decide))

theorem FPre.keyD {d n : Nat} (h : d + n ≤ 400) {r : Region} (hr : Region.Sub r ⟨S, 120⟩) :
    (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right hr

theorem full_wp (hL : L = 8) {s : State} (h : P1 s₀ W St P S s) :
    WP isa (.block full) s (BPost s₀ W St P S L) := by
  subst hL
  have kw := hp.key_wrap
  obtain ⟨s', run, ax, g, m, rd, wr⟩ := xor1_ok s .rdx .rdi 0 384 (P := P) (Q := W + BitVec.ofNat 64 384)
    (by rw [h.rdx]; simp) (by rw [h.rdi]) (by decide)
    (by rw [h.rd, h.wr]; simpa using hp.inLast (d := 0) (n := 8) (by decide))
    (by rw [h.rd, h.wr]; exact hp.inKey (d := 384) (n := 8) (by decide))
  refine WP.of_runBlock ⟨s', run, by rw [g _ (by decide), h.r14], by rw [g _ (by decide), h.r15],
    by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.rsp], by rw [rd, h.rd], by rw [wr, h.wr],
    by rw [m, h.mem]; exact Frame.refl _ _, ?_⟩
  obtain fs := savedMem_frame s₀ S
  rw [ax, h.mem, le8_xor, le8_readW, le8_readW,
    bytesAt_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.last_scr.sub_right (FPre.scrD (by decide))) (by decide),
    bytesAt_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.keyD (d := 384) (n := 8) (by decide) (FPre.scrD (by decide))) (by decide)]
  simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, ite_true]
  exact xor_comm _ _

open VG.WriteBytes in
theorem partial_wp (hL : L < 8) {s : State} (h : P1 s₀ W St P S s) :
    WP isa partialBlock s (BPost s₀ W St P S L) := by
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  obtain hcx : s.gpr .rcx = BitVec.ofNat 64 L := by
    rw [h.rcx, ← hp.rcx]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨C, hC⟩ : ∃ C, S + BitVec.ofNat 64 96 = C := ⟨_, rfl⟩
  obtain hc : s.gpr .r15 + BitVec.ofNat 64 96 = C := by rw [h.r15, hC]
  obtain dPC : (⟨P, L⟩ : Region).Disjoint ⟨C, 8⟩ := by rw [← hC]; exact hp.last_scr.sub_right (FPre.scrD (by decide))
  obtain sl : slot12 S = ⟨C, 8⟩ := by rw [← hC]
  -- Zero the slot.
  obtain ⟨s₁, run₁, zf₁, mem₁, g₁, rd₁, wr₁⟩ := zero_ok s hc hcx (by omega_using [hL])
    (by rw [h.wr, ← hC]; exact hp.inScr (d := 96) (n := 8) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  let m₁ := (savedMem s₀ S).writeW C (BitVec.setWidth 64 (0 : BitVec 32))
  obtain zf : s₁.mem = m₁ := by rw [mem₁, h.mem]
  obtain fz : Frame [⟨C, 8⟩] (savedMem s₀ S) m₁ :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain lastS : Spec.Aes.bytesAt (savedMem s₀ S) P L = Spec.Aes.bytesAt s₀.mem P L :=
    bytesAt_frame (savedMem_frame s₀ S) (hp.save_frame) (by omega_using [hL])
  obtain lastZ : Spec.Aes.bytesAt m₁ P L = Spec.Aes.bytesAt s₀.mem P L := by
    rw [bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega_using [hL]),
      lastS]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.mem = writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s₂.gpr r = s.gpr r) ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr) ?_ fun s₂ h₂ => ?_)
  · by_cases hL0 : L = 0
    · subst hL0
      refine WP.ite true (by show s₁.zf = _; rw [zf₁]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [zf]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r h₁ _ => g₁ r h₁,
        by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩
    · refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_ok s₁ (by omega_using [hL0]) hL (by rw [g₁ _ (by decide), h.rdx])
        (by rw [g₁ _ (by decide)]; exact hc) (by rw [g₁ _ (by decide)]; exact hcx)
        (fun i hi => by rw [rd₁, wr₁, h.rd, h.wr]; exact hp.inLast (d := i) (n := 1) (by omega_using [hi]))
        (fun i hi => by
          rw [wr₁, h.wr, ← hC, Offset.add_add]; exact hp.inScr (d := 96 + i) (n := 1) (by omega_using [hi])) dPC) ?_
      rintro s₂ ⟨m₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, zf, lastZ], fun r h₁ h₂ => by rw [g₂ r h₁ h₂, g₁ r h₁], by rw [rd₂, rd₁, h.rd],
        by rw [wr₂, wr₁, h.wr]⟩
  · obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
    obtain r15₂ : s₂.gpr .r15 = S := by rw [g₂ _ (by decide) (by decide), h.r15]
    obtain rcx₂ : s₂.gpr .rcx = BitVec.ofNat 64 L := by rw [g₂ _ (by decide) (by decide), hcx]
    obtain rdi₂ : s₂.gpr .rdi = W := by rw [g₂ _ (by decide) (by decide), h.rdi]
    obtain ⟨s₃, run₃, m₃, ax₃, g₃, rd₃, wr₃⟩ := pad_ok s₂ (C := C) (K := W + BitVec.ofNat 64 392) (L := L)
      (by rw [r15₂, rcx₂, BitVec.mul_one, show BitVec.ofInt 64 96 = BitVec.ofNat 64 96 from rfl, ← hC,
        BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L), ← BitVec.add_assoc])
      (by rw [r15₂, hC]) (by rw [rdi₂])
      (by rw [wr₂, ← hC, Offset.add_add]; exact hp.inScr (d := 96 + L) (n := 1) (by omega_using [hL]))
      (by rw [rd₂, wr₂, ← hC]; exact wr_in (hp.inScr (d := 96) (n := 8) (by decide)))
      (by rw [rd₂, wr₂]; exact hp.inKey (d := 392) (n := 8) (by decide))
    refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
    have gg (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .r10) : s₃.gpr r = s.gpr r := by rw [g₃ r h₁, g₂ r h₁ h₂]
    obtain hlen : (Spec.Aes.bytesAt s₀.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    obtain fB : Frame [⟨C, 8⟩] m₁ (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) :=
      writeBytes_frame _ _ _ (by
        rw [hlen]; simpa using Offset.contains_base C (d := 0) (n := L) (k := 8) (by omega_using [hL]) (by decide))
    obtain fW : Frame [⟨C, 8⟩] (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem P L)) s₃.mem := by
      rw [m₃, m₂]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hL]) (by omega_using [hL]))
    obtain f₃ : Frame [⟨C, 8⟩] (savedMem s₀ S) s₃.mem := (fz.trans fB).trans fW
    obtain kD : (⟨W + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint ⟨C, 8⟩ := by
      rw [← hC]; exact hp.keyD (by decide) (FPre.scrD (by decide))
    obtain k2 : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 392) 8 =
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 := by
      rw [bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide),
        bytesAt_frame (savedMem_frame s₀ S) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.keyD (d := 392) (n := 8) (by decide) (FPre.scrD (by decide))) (by decide)]
    obtain pad : Spec.Aes.bytesAt s₃.mem C 8 =
        Spec.Aes.bytesAt s₀.mem P L ++ [0x80] ++ Spec.Cmac.zeros (8 - L - 1) := by
      obtain hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
        rw [← le8_readW, Mem.readW_writeW_self64]; decide
      have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem P L) (by rw [hlen]; exact hL) hz
      rw [hlen] at this
      rw [m₃, m₂]; exact this
    refine ⟨by rw [gg _ (by decide) (by decide), h.r14], by rw [gg _ (by decide) (by decide), h.r15],
      by rw [gg _ (by decide) (by decide), h.rbp], by rw [gg _ (by decide) (by decide), h.rsp],
      by rw [rd₃, rd₂], by rw [wr₃, wr₂], by rw [sl]; exact f₃, ?_⟩
    rw [ax₃, ← m₃, le8_xor, le8_readW, le8_readW, pad, k2]
    simp only [mn, Spec.Cmac.lastBlock, hlen, show L ≠ 8 by omega_using [hL], ite_false]
    exact xor_comm _ _

end

theorem finPre_wp {s₀ : State} {W St P S : Addr} {L : Nat} (hp : FPre s₀ W St P S L) :
    WP isa finPre s₀ (BPost s₀ W St P S L) := by
  obtain hcx : s₀.gpr .rcx = BitVec.ofNat 64 L := by rw [← hp.rcx]; apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨s₁, run₁, r15₁, r14₁, rbp₁, g₁, zf₁, m₁, rd₁, wr₁⟩ :=
    pre1_ok s₀ (fun d _ h => by rw [hp.r8]; exact hp.inScr (by omega_using [h])) hcx hp.len
  obtain h1 : P1 s₀ W St P S s₁ := ⟨by rw [r15₁, hp.r8], by rw [r14₁, hp.rdi], by rw [rbp₁, hp.rsi],
    by rw [g₁ _ (by decide), hp.rdi], by rw [g₁ _ (by decide), hp.rdx], g₁ _ (by decide),
    g₁ _ (by decide), by rw [m₁, hp.r8], rd₁, wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases hL : L = 8
  · exact WP.ite true (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun _ => full_wp hp hL h1) (fun h => by cases h)
  · exact WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega_using [hL, this]) h1)

theorem xorSt_ok (s : State) {St : Addr} (hb : s.gpr .rbp = St) (r : InRegions (s.rd ++ s.wr) St 8) :
    ∃ s', runBlock isa [.alu .xor .rax (.mem (at_ .rbp 0)), .bswap .rax] s = some s' ∧
      s'.gpr .rax = byteRev64 (s.gpr .rax ^^^ s.mem.readW St 64) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.ea, offset_nat, Option.bind_some, hb, BitVec.add_zero, r,
      ]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, bswap64_eq]
  · simp [gpr_setReg, hr]

theorem storeSt_ok (s : State) {St : Addr} (hb : s.gpr .rbp = St) (w : InRegions s.wr St 8) :
    ∃ s', runBlock isa [.bswap .rax, .store (at_ .rbp 0) .rax] s = some s' ∧
      s'.mem = s.mem.writeW St (byteRev64 (s.gpr .rax)) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      State.store64, State.ea, offset_nat, gpr_setReg, rd_setReg, wr_setReg, hb,
      BitVec.add_zero, w]
    rfl, ?_⟩
  refine ⟨by simp [mem_setReg, bswap64_eq], fun r hr => ?_, rfl, rfl⟩
  simp [gpr_setReg, hr]

theorem finalize_wp {s₀ : State} (h0 : finalizeX86_64.pre s₀) :
    WP isa finalize s₀ fun s' => gprPreserved s₀ s' ∧ finalizeX86_64.post s₀ s' := by
  obtain hp := FPre.of h0
  generalize hW : s₀.gpr .rdi = W at hp
  generalize hSt : s₀.gpr .rsi = St at hp
  generalize hP : s₀.gpr .rdx = P at hp
  generalize hS : s₀.gpr .r8 = S at hp
  generalize hL : (s₀.gpr .rcx).toNat = L at hp
  have sw := hp.scr_wrap
  have kw := hp.key_wrap
  have tw := hp.st_wrap
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  obtain rdwr₁ : s₁.rd ++ s₁.wr = [⟨W, 400⟩, ⟨P, L⟩, ⟨St, 8⟩, ⟨S, 120⟩] := by rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₂, run₂, ax₂, g₂, m₂, rd₂, wr₂⟩ := xorSt_ok s₁ h₁.rbp
    (by rw [rdwr₁]; exact in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain bp : BlockPre s₂ :=
    { sched := ⟨⟨W, 400⟩, by rw [rd₂, h₁.rd, hp.rd]; simp, by rw [g₂ _ (by decide), h₁.r14],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨S, 120⟩, by rw [wr₂, h₁.wr, hp.wr]; simp, by rw [g₂ _ (by decide), h₁.r15],
        by show 48 ≤ 120; decide, by show 120 < 2 ^ 64; decide⟩
      disj := by
        rw [g₂ _ (by decide), g₂ _ (by decide), h₁.r14, h₁.r15]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right
          (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₃ ⟨same₃, r14₃, ax₃⟩ => ?_)
  rw [WP.block_append_iff]
  obtain rbp₃ : s₃.gpr .rbp = St := by rw [same₃.rbp, g₂ _ (by decide), h₁.rbp]
  obtain r15₃ : s₃.gpr .r15 = S := by rw [same₃.r15, g₂ _ (by decide), h₁.r15]
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := storeSt_ok s₃ rbp₃
    (by rw [same₃.wr, wr₂, h₁.wr, hp.wr]; exact in_rw (r := ⟨St, 8⟩) (by simp) (Region.contains_self _ _))
  obtain rdwr₄ : s₄.rd ++ s₄.wr = [⟨W, 400⟩, ⟨P, L⟩, ⟨St, 8⟩, ⟨S, 120⟩] := by
    rw [rd₄, wr₄, same₃.rd, same₃.wr, rd₂, wr₂, rdwr₁]
  obtain ⟨s₅, run₅, b, c, d, e, f, g, rsp₅, m₅⟩ := restore_ok s₄ (by rw [g₄ _ (by decide), r15₃]) fun d _ h₂' => by
    rw [rdwr₄]; exact in_rw (r := ⟨S, 120⟩) (by simp) (Offset.contains_base _ (by omega_using [h₂']) (by omega_using [h₂']))
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  -- Memory.
  obtain xR₂ : xR s₂ = ⟨S, 48⟩ := by rw [xR, g₂ _ (by decide), h₁.r15]
  obtain f₃ : Frame [⟨S, 48⟩] s₁.mem s₃.mem := by rw [← m₂, ← xR₂]; exact same₃.frame
  obtain f₄ : Frame [⟨St, 8⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fAll : Frame [slot12 S, ⟨S, 48⟩, ⟨St, 8⟩] (savedMem s₀ S) s₅.mem := by
    rw [m₅]
    exact ((h₁.frame.mono fun r hr => by simp at hr; simp [hr]).trans (f₃.mono fun r hr => by
      simp at hr; simp [hr])).trans (f₄.mono fun r hr => by simp at hr; simp [hr])
  obtain big : Frame [⟨S, 120⟩, ⟨St, 8⟩] s₀.mem s₅.mem :=
    ((savedMem_frame s₀ S).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨S, 120⟩, by simp, FPre.scrD (by decide)⟩).trans (fAll.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨S, 120⟩, by simp, FPre.scrD (by decide)⟩
      · exact ⟨⟨S, 120⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨St, 8⟩, by simp, fun _ h => h⟩)
  obtain hm : ∀ d, 48 ≤ d → d + 8 ≤ 96 →
      s₄.mem.readW (S + BitVec.ofNat 64 d) 64 = (savedMem s₀ S).readW (S + BitVec.ofNat 64 d) 64 := by
    intro d h₁' h₂'
    rw [← m₅]
    refine fAll.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (d := d) (e := 96) (by omega_using [h₂']) (by omega_using [h₂']) (by omega_using [])
    · exact Offset.disjoint_base _ (by omega_using [h₁']) (by omega_using [h₂'])
    · exact (hp.st_scr.sub_right (FPre.scrD (by omega_using [h₂']))).symm
  refine ⟨⟨restored (S := S) hm ⟨b, c, d, e, f, g⟩ (by rw [rsp₅, g₄ _ (by decide), same₃.rsp,
    g₂ _ (by decide), h₁.rsp]), ?_⟩, ?_⟩
  · refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_scr
    · exact hp.ret_st
  · intro hk msg hml hne hst
    rw [hW, hSt, hP, hL] at *
    have keyD (r : Region) (hr : Region.Sub r ⟨S, 120⟩) : (⟨W, 384⟩ : Region).Disjoint r :=
      (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right hr
    obtain f₁ : Frame [⟨S + BitVec.ofNat 64 48, 48⟩, slot12 S] s₀.mem s₁.mem :=
      ((savedMem_frame s₀ S).mono fun r hr => by simp at hr; simp [hr]).trans
        (h₁.frame.mono fun r hr => by simp at hr; simp [hr])
    obtain hS' : sch s₂ = Spec.TripleDes.scheduleAt s₀.mem W := by
      rw [sch, g₂ _ (by decide), h₁.r14, m₂]
      exact scheduleAt_frame f₁ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact keyD _ (FPre.scrD (by decide))
        · exact keyD _ (FPre.scrD (by decide))
    obtain hst₁ : le8 (s₁.mem.readW St 64) = Spec.Aes.bytesAt s₀.mem St 8 := by
      rw [le8_readW]
      exact bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_scr.sub_right (FPre.scrD (by decide))
        · exact hp.st_scr.sub_right (FPre.scrD (by decide))) (by decide)
    obtain hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem W)
    obtain hk' : Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 384) 8 ++
        Spec.Aes.bytesAt s₀.mem (W + BitVec.ofNat 64 392) 8 =
        (Spec.Cmac.subkeys (ciphAt s₀.mem W) 8).1 ++ (Spec.Cmac.subkeys (ciphAt s₀.mem W) 8).2 := by
      rw [show W + BitVec.ofNat 64 392 = W + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
        (Offset.add_add W 384 8).symm, ← bytesAt_split]; exact hk
    obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, ciphAt, hks, length_le8])
    show Spec.Aes.bytesAt s₅.mem St 8 = _
    rw [m₅, m₄, ← le8_readW, Mem.readW_writeW_self64, ax₃, ax₂, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
      macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, xor_comm]

end VG.Proof.CmacTripleDes.X86_64

end

end

/-!
# TDEA-CMAC on x86-64: correctness

Correctness under this target's contracts (`Contract.lean`), with no stack:
the functions call nothing.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.X86_64

theorem init_mx : init.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem update_mx : update.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem finalize_mx : finalize.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem init_correct (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec init_mx he hg, hp⟩

theorem update_correct (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := update_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec update_mx he hg, hp⟩

theorem finalize_correct (s : State) (hs : finalizeX86_64.pre s) :
    ∃ t s', Exec isa finalize s t s' ∧ abiPreserved s s' ∧ finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalize_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec finalize_mx he hg, hp⟩

end VG.Proof.CmacTripleDes.X86_64

end

end

/-!
# Streaming TDEA-CMAC on x86-64: the code of `init`, `update` and `finalize`, inline

Each run of the code of `vg_cmac_triple_des_init`, `_update` and `_finalize`
inside the streaming functions, from its contract (`WP.inline`): what it
needs (`…Args`), and what it leaves (`…Post`, in terms of the memory before
it): it changes memory only in its buffers, and keeps our caller's
callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64
open VG.Proof.CmacTripleDes.X86_64 (updateX86_64 finalizeX86_64 initX86_64 ciphAt)

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## `update` -/

/-- What a run of `update` needs: the key schedule `W`, the chaining value
`C`, `n` blocks at `D` and the working space `S`. -/
structure UArgs (s : State) (W C D S : Addr) (n : Nat) : Prop where
  rdi : s.gpr .rdi = W
  rsi : s.gpr .rsi = C
  rdx : s.gpr .rdx = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  r8 : s.gpr .r8 = S
  hn : 8 * n < 2 ^ 64
  wc : (⟨W, 384⟩ : Region).Disjoint ⟨C, 8⟩
  ws : (⟨W, 384⟩ : Region).Disjoint ⟨S, 120⟩
  dc : (⟨D, 8 * n⟩ : Region).Disjoint ⟨C, 8⟩
  ds : (⟨D, 8 * n⟩ : Region).Disjoint ⟨S, 120⟩
  cs : (⟨C, 8⟩ : Region).Disjoint ⟨S, 120⟩
  retC : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 8⟩
  retS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 120⟩
  wrapC : C.toNat + 8 ≤ 2 ^ 64
  wrapD : D.toNat + 8 * n ≤ 2 ^ 64
  wrapS : S.toNat + 120 ≤ 2 ^ 64
  reads : Covers ([⟨W, 384⟩, ⟨D, 8 * n⟩] ++ [⟨C, 8⟩, ⟨S, 120⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 8⟩, ⟨S, 120⟩] s.wr

/-- What a run of `update` leaves. -/
structure UPost (s : State) (W C D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C, 8⟩, ⟨S, 120⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem C 8 =
    Spec.Cmac.chain (ciphAt s.mem W) (Spec.Aes.bytesAt s.mem C 8) (Spec.Cmac.blocksAt s.mem D 8 n)

theorem UArgs.pre {s : State} {W C D S : Addr} {n : Nat} (h : UArgs s W C D S n) :
    updateX86_64.pre (s.withRegions [⟨W, 384⟩, ⟨D, 8 * n⟩] [⟨C, 8⟩, ⟨S, 120⟩]) := by
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega_using [this])
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.rdi,
    h.rsi, h.rdx, h.rcx, h.r8, hN]
  exact ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.retC, h.retS, h.wrapC, h.wrapD, h.wrapS⟩

theorem upd_wp {s : State} {W C D S : Addr} {n : Nat} (h : UArgs s W C D S n) :
    WP isa Impl.CmacTripleDes.X86_64.update s (UPost s W C D S n) := by
  have hN := toNat_ofNat (n := n) (by have := h.hn; omega_using [this])
  refine WP.inline (k := updateX86_64) Proof.CmacTripleDes.X86_64.update_correct h.pre h.reads h.writes
    (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [updateX86_64, State.withRegions_gpr, State.withRegions_mem, h.rdi, h.rsi, h.rdx, h.rcx,
    hN] at hpost
  exact hpost

/-! ## `finalize` -/

/-- What a run of `finalize` needs: the key schedule and subkeys `K`, the
state `St`, the `L` last bytes at `P` and the working space `S`. -/
structure FArgs (s : State) (K St P S : Addr) (L : Nat) : Prop where
  rdi : s.gpr .rdi = K
  rsi : s.gpr .rsi = St
  rdx : s.gpr .rdx = P
  rcx : s.gpr .rcx = BitVec.ofNat 64 L
  r8 : s.gpr .r8 = S
  len : L ≤ 8
  kst : (⟨K, 400⟩ : Region).Disjoint ⟨St, 8⟩
  ks : (⟨K, 400⟩ : Region).Disjoint ⟨S, 120⟩
  pst : (⟨P, L⟩ : Region).Disjoint ⟨St, 8⟩
  ps : (⟨P, L⟩ : Region).Disjoint ⟨S, 120⟩
  sts : (⟨St, 8⟩ : Region).Disjoint ⟨S, 120⟩
  retSt : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 8⟩
  retS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 120⟩
  wrapK : K.toNat + 400 ≤ 2 ^ 64
  wrapSt : St.toNat + 8 ≤ 2 ^ 64
  wrapP : P.toNat + L ≤ 2 ^ 64
  wrapS : S.toNat + 120 ≤ 2 ^ 64
  reads : Covers ([⟨K, 400⟩, ⟨P, L⟩] ++ [⟨St, 8⟩, ⟨S, 120⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨St, 8⟩, ⟨S, 120⟩] s.wr

/-- What a run of `finalize` leaves. -/
structure FPost (s : State) (K St P S : Addr) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St, 8⟩, ⟨S, 120⟩] s.mem s'.mem
  out : let ciph := ciphAt s.mem K
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (K + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem St 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem St 8 = Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem P L)

theorem FArgs.pre {s : State} {K St P S : Addr} {L : Nat} (h : FArgs s K St P S L) :
    finalizeX86_64.pre (s.withRegions [⟨K, 400⟩, ⟨P, L⟩] [⟨St, 8⟩, ⟨S, 120⟩]) := by
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_using [this])
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.rdi,
    h.rsi, h.rdx, h.rcx, h.r8, hL]
  exact ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.retSt, h.retS, h.wrapK, h.wrapSt, h.wrapP,
    h.wrapS, h.len⟩

theorem fin_wp {s : State} {K St P S : Addr} {L : Nat} (h : FArgs s K St P S L) :
    WP isa Impl.CmacTripleDes.X86_64.finalize s (FPost s K St P S L) := by
  have hL := toNat_ofNat (n := L) (by have := h.len; omega_using [this])
  refine WP.inline (k := finalizeX86_64) Proof.CmacTripleDes.X86_64.finalize_correct h.pre h.reads
    h.writes (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [finalizeX86_64, State.withRegions_gpr, State.withRegions_mem, h.rdi, h.rsi, h.rdx, h.rcx,
    hL] at hpost
  exact hpost

/-! ## `init` -/

/-- What a run of `init` needs: the key `Kp` of `KL` bytes, the output `O`
and the working space `S`. -/
structure IArgs (s : State) (Kp O S : Addr) (KL : Nat) : Prop where
  rdi : s.gpr .rdi = Kp
  rsi : s.gpr .rsi = BitVec.ofNat 64 KL
  rdx : s.gpr .rdx = O
  rcx : s.gpr .rcx = S
  klen : Spec.TripleDes.validKey KL
  ko : (⟨Kp, KL⟩ : Region).Disjoint ⟨O, 400⟩
  ks : (⟨Kp, KL⟩ : Region).Disjoint ⟨S, 120⟩
  os : (⟨O, 400⟩ : Region).Disjoint ⟨S, 120⟩
  retO : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 400⟩
  retS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 120⟩
  wrapK : Kp.toNat + KL ≤ 2 ^ 64
  wrapO : O.toNat + 400 ≤ 2 ^ 64
  wrapS : S.toNat + 120 ≤ 2 ^ 64
  reads : Covers ([⟨Kp, KL⟩] ++ [⟨O, 400⟩, ⟨S, 120⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨O, 400⟩, ⟨S, 120⟩] s.wr

/-- What a run of `init` leaves. -/
structure IPost (s : State) (Kp O S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨O, 400⟩, ⟨S, 120⟩] s.mem s'.mem
  out : let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem Kp KL)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem O = k ∧ Spec.Aes.bytesAt s'.mem (O + 384) 16 = ks.1 ++ ks.2

theorem IArgs.pre {s : State} {Kp O S : Addr} {KL : Nat} (h : IArgs s Kp O S KL) :
    initX86_64.pre (s.withRegions [⟨Kp, KL⟩] [⟨O, 400⟩, ⟨S, 120⟩]) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h <;> omega_using [h])
  simp only [initX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, h.rdi,
    h.rsi, h.rdx, h.rcx, hK]
  exact ⟨trivial, trivial, h.ko, h.ks, h.os, h.retO, h.retS, h.wrapK, h.wrapO, h.wrapS, h.klen⟩

theorem init_inline_wp {s : State} {Kp O S : Addr} {KL : Nat} (h : IArgs s Kp O S KL) :
    WP isa Impl.CmacTripleDes.X86_64.init s (IPost s Kp O S KL) := by
  have hK := toNat_ofNat (n := KL) (by rcases h.klen with h | h <;> omega_using [h])
  refine WP.inline (k := initX86_64) Proof.CmacTripleDes.X86_64.init_correct h.pre h.reads h.writes
    (fun s' hrd hwr ha hf _ hpost => ⟨hrd, hwr, ha.1, hf, ?_⟩) (by lit_decide)
  simp only [initX86_64, State.withRegions_gpr, State.withRegions_mem, h.rdi, h.rsi, h.rdx, hK] at hpost
  exact hpost

end VG.Proof.CmacTripleDes.Stream.X86_64

end

end

/-!
# Streaming TDEA-CMAC on x86-64: arithmetic, memory and copying bytes

The number of bytes held back, as the code computes it from `count`
(`held_bv`); the bytes `writeBytes` leaves; and `copy`, which copies the
`rcx` bytes at `r13` to `rdx`, a byte at a time (none if `rcx` is 0),
changing only `rax`, `r10` and the flags.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.CmacTripleDes.Stream (held held_pos held_zero)

/-! ## Arithmetic -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide
theorem sx400 : BitVec.signExtend 64 (400 : BitVec 32) = BitVec.ofNat 64 400 := by decide
theorem sx408 : BitVec.signExtend 64 (408 : BitVec 32) = BitVec.ofNat 64 408 := by decide

theorem and7 (x : BitVec 64) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero `count`, as `sub 1; and 7; add 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - 1) &&& 7) + 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega_using [hc])]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and7, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  have := c.isLt
  omega_using [hc]

theorem beq_zero_iff (c : BitVec 64) : (c == 0) = decide (c.toNat = 0) := by
  by_cases h : c = 0
  · subst h; rfl
  · have : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simpa [this] using h

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, hd] : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega_using [h, hd])

/-! ## Bytes written -/

section
open VG.WriteBytes

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega_using [h])]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega_using [h])

end

/-! ## Copying bytes -/

section
open VG.Impl.CmacTripleDes.Stream.X86_64 VG.WriteBytes
open VG.Proof.CmacTripleDes.X86_64 (succ_ofNat bytesAt_succ)

theorem copyStep_ok (s : State) {P C : Addr} {i L : Nat} (hc : s.gpr .r13 = P) (hd : s.gpr .rdx = C)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (h8 : s.gpr .rcx = BitVec.ofNat 64 L)
    (r : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (C + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (C + BitVec.ofNat 64 i) (s.mem (P + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ : s.gpr .r13 + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = P + BitVec.ofNat 64 i := by
    rw [hc, hi, BitVec.mul_one]; simp
  have ea₂ : s.gpr .rdx + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = C + BitVec.ofNat 64 i := by
    rw [hd, hi, BitVec.mul_one]; simp
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, BitVec.reduceSignExtend, copyBody, srcByte, dstByte, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, 
      ea₁, ea₂, r, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hi]
  · simp [hi, h8]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  · rfl
  · rfl

/-- What `copy` leaves. -/
structure Copied (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (hc : s.gpr .r13 = P)
    (hd : s.gpr .rdx = C) (h8 : s.gpr .rcx = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa copy s (Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  obtain ⟨s₁, run₁, r10₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁,
      runBlock isa [.mov32 .r10 (.imm 0), .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁.zf = some (decide (L = 0)) ∧
      (∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        State.setReg32, Option.map_some, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
      mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, reduceCtorEq, ↓reduceIte,
      and_self, BitVec.reduceSetWidth, BitVec.and_self, h8, beq_zero_iff, toNat_ofNat hL]
    exact ⟨trivial, trivial, fun r h => by simp [h], trivial⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by show s₁.zf = _; rw [zf₁]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [m₁]; simp [Spec.Aes.bytesAt, writeBytes_nil], fun r _ h => g₁ r h, rd₁, wr₁⟩
  refine WP.ite false (by show s₁.zf = _; rw [zf₁]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, by omega_using [hL0], r10₁, by rw [m₁]; simp [Spec.Aes.bytesAt, writeBytes_nil],
      fun r _ h₂ => g₁ r h₂, rd₁, wr₁⟩
  rintro n t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t
    (by rw [g _ (by decide) (by decide), hc]) (by rw [g _ (by decide) (by decide), hd]) r10
    (by rw [g _ (by decide) (by decide), h8])
    (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i hi)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) = s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdis _ (Offset.contains_base P (by omega_using [hi]) (by omega_using [hL, hi])) (Region.sub_prefix (by omega_using [hi]) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, bytesAt_succ, writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i)
      (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega_using [hL, hi]), hlen]
  have hz : t'.zf = some (decide (i + 1 = L)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega_using [hL, hi]) (by omega_using [hL])]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = L
  · left
    exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], L - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], by rw [r10', succ_ofNat], hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end

end VG.Proof.CmacTripleDes.Stream.X86_64
