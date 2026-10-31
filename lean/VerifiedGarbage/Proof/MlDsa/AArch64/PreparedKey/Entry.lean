module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Public
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.SecretAll
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.Mem

/-! # Prepared-key entry layouts -/

-- separate module: separates signature and stack-layout facts, shared by ABI and timing wrappers.

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa

structure EntryPre (bytes count : Nat) (s : State) : Prop where
  stack : 80 ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x0, bytes⟩]
  wr : s.wr = [⟨s.gpr .x1, bytes + 1024 * count⟩, ⟨s.gpr .x2, 1024⟩]
  io : Region.Disjoint ⟨s.gpr .x0, bytes⟩ ⟨s.gpr .x1, bytes + 1024 * count⟩
  it : Region.Disjoint ⟨s.gpr .x0, bytes⟩ ⟨s.gpr .x2, 1024⟩
  ot : Region.Disjoint ⟨s.gpr .x1, bytes + 1024 * count⟩ ⟨s.gpr .x2, 1024⟩
  si : (below s.sp 80).Disjoint ⟨s.gpr .x0, bytes⟩
  so : (below s.sp 80).Disjoint ⟨s.gpr .x1, bytes + 1024 * count⟩
  st : (below s.sp 80).Disjoint ⟨s.gpr .x2, 1024⟩
  ni : (s.gpr .x0).toNat + bytes ≤ 2 ^ 64
  no : (s.gpr .x1).toNat + bytes + 1024 * count ≤ 2 ^ 64
  nt : (s.gpr .x2).toNat + 1024 ≤ 2 ^ 64

theorem public_pre {p : Params} {s : State}
    (hpre : (preparePublicKeyContract p AArch64.abi 80).pre s) : EntryPre p.pkLen p.k s := by
  sig_pre [preparePublicKeyContract, preparePublicKeySig, AArch64.abi,
    VG.AArch64.argRegs] at hpre
  obtain ⟨hsp, hr, hw, hio, hit, hot, hsi, hso, hst, hni, hno, hnt⟩ := hpre
  exact ⟨hsp, hr, hw, hio, hit, hot, hsi, hso, hst, hni, by simpa only [Nat.add_assoc, preparedPublicKeyBytes, n] using hno, hnt⟩

theorem secret_pre {p : Params} {s : State}
    (hpre : (prepareSecretKeyContract p AArch64.abi 80).pre s) : EntryPre p.skLen (p.ℓ + 2 * p.k) s := by
  sig_pre [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi,
    VG.AArch64.argRegs] at hpre
  obtain ⟨hsp, hr, hw, hio, hit, hot, hsi, hso, hst, hni, hno, hnt⟩ := hpre
  exact ⟨hsp, hr, hw, hio, hit, hot, hsi, hso, hst, hni, by simpa only [Nat.add_assoc, preparedSecretKeyBytes, n] using hno, hnt⟩

theorem public_sp {p : Params} {s : State}
    (hpre : (preparePublicKeyContract p AArch64.abi 80).pre s) : 80 ≤ s.sp.toNat := by
  sig_pre [preparePublicKeyContract, preparePublicKeySig, AArch64.abi,
    VG.AArch64.argRegs] at hpre
  exact KeyGen.le_of_wfP hpre.1

theorem secret_sp {p : Params} {s : State}
    (hpre : (prepareSecretKeyContract p AArch64.abi 80).pre s) : 80 ≤ s.sp.toNat := by
  sig_pre [prepareSecretKeyContract, prepareSecretKeySig, AArch64.abi,
    VG.AArch64.argRegs] at hpre
  exact KeyGen.le_of_wfP hpre.1

theorem entry_layout_covers {bytes count : Nat} {σ s : State} (h : EntryPre bytes count σ)
    (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32)
    (hr : Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr)) (hw : Covers σ.wr s.wr)
    (hsp : s.sp = σ.sp - 64)
    (h25 : s.gpr .x25 = σ.gpr .x0) (h26 : s.gpr .x26 = σ.gpr .x1)
    (h28 : s.gpr .x28 = σ.gpr .x2) :
    Lay 16 (input bytes) (output bytes count) s := by
  have hstk : Region.Sub (below s.sp 16) (below σ.sp 80) := by
    rw [hsp]
    exact below_below σ.sp 64 16
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro b hb'
    simp only [input, output, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    exacts [hb, ho, by decide]
  · intro b hb' b' hb'' hne _
    simp only [input, output, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hb' hb''
    rcases hb' with rfl | rfl | rfl <;> rcases hb'' with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | simp only [h25, h26, h28]
        first | exact h.io | exact h.it | exact h.ot | exact h.io.symm | exact h.it.symm | exact h.ot.symm
  · intro b hb'
    simp only [input, output, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl <;> simp only [h25, h26, h28]
    exacts [h.si.sub_left hstk, h.so.sub_left hstk, h.st.sub_left hstk]
  · intro b hb'
    simp only [input, output, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl <;> simp only [h25, h26, h28]
    exacts [h.ni, by simpa only [Nat.add_assoc] using h.no, h.nt]
  · intro b hb'
    simp only [input, output, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl <;> simp only [h25, h26, h28]
    all_goals apply hr; rw [h.rd, h.wr]
    exacts [KeyGen.inR_self (r := ⟨σ.gpr .x0, bytes⟩) (by simp),
      KeyGen.inR_self (r := ⟨σ.gpr .x1, bytes + 1024 * count⟩) (by simp),
      KeyGen.inR_self (r := ⟨σ.gpr .x2, 1024⟩) (by simp)]
  · intro b hb'
    simp only [output, List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl <;> simp only [h26, h28]
    all_goals apply hw; rw [h.wr]
    exacts [KeyGen.inR_self (r := ⟨σ.gpr .x1, bytes + 1024 * count⟩) (by simp),
      KeyGen.inR_self (r := ⟨σ.gpr .x2, 1024⟩) (by simp)]
  · intro b hb'
    simp only [input, output, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl <;> simp [keptRegs]
  · rw [hsp]
    change 16 ≤ (σ.sp - BitVec.ofNat 64 64).toNat
    rw [toNat_sub_ofNat' (by have := h.stack; omega)]
    have := h.stack
    omega

theorem entry_layout {bytes count : Nat} {σ s : State} (h : EntryPre bytes count σ)
    (hb : bytes < 2 ^ 32) (ho : bytes + 1024 * count < 2 ^ 32)
    (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) (hsp : s.sp = σ.sp - 64)
    (h25 : s.gpr .x25 = σ.gpr .x0) (h26 : s.gpr .x26 = σ.gpr .x1)
    (h28 : s.gpr .x28 = σ.gpr .x2) :
    Lay 16 (input bytes) (output bytes count) s :=
  entry_layout_covers h hb ho (by rw [hr, hw]; exact Covers.refl _)
    (by rw [hw]; exact Covers.refl _) hsp h25 h26 h28

theorem frame_guards {bytes count : Nat} {σ s : State} (h : EntryPre bytes count σ)
    {offset : Nat} (ho : offset ≤ 64) (hr : s.wr = σ.wr)
    (hsp : s.sp = σ.sp - BitVec.ofNat 64 offset) :
    16 ≤ s.sp.toNat ∧ ∀ R ∈ s.wr, Region.Disjoint ⟨s.sp - 16, 16⟩ R := by
  have hs : Region.Sub (⟨s.sp - 16, 16⟩ : Region) (below σ.sp 80) := by
    have h1 := below_below σ.sp offset 16
    have h2 := below_sub (sp := σ.sp) (a := 16 + offset) (b := 80) (by omega) (by decide)
    rw [hsp]
    exact fun a ha => h2 a (h1 a ha)
  refine ⟨?_, ?_⟩
  · rw [hsp, toNat_sub_ofNat' (by have := h.stack; omega)]
    have := h.stack
    omega
  · intro R hR
    rw [hr, h.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [h.so.sub_left hs, h.st.sub_left hs]

def pushState (r : Reg) (s : State) : State :=
  {s with sp := s.sp - 16, mem := s.mem.write (s.sp - 16) 8 (s.gpr r)}

def innerState (s : State) : State :=
  pushState .x30 (pushState .x28 (pushState .x26 (pushState .x25 s)))

theorem inner_rd (s : State) : (innerState s).rd = s.rd := rfl
theorem inner_wr (s : State) : (innerState s).wr = s.wr := rfl

theorem inner_sp (s : State) : (innerState s).sp = s.sp - 64 := by
  simp only [innerState, pushState, BitVec.sub_sub]
  rfl

theorem push_source {bytes count : Nat} {σ s : State} (h : EntryPre bytes count σ)
    (hb : bytes < 2 ^ 32) {offset : Nat} (ho : offset ≤ 64)
    (hsp : s.sp = σ.sp - BitVec.ofNat 64 offset) (r : Reg) :
    VG.Spec.Sha3.bytesAt (pushState r s).mem (σ.gpr .x0) bytes =
      VG.Spec.Sha3.bytesAt s.mem (σ.gpr .x0) bytes := by
  have hs : Region.Sub (⟨s.sp - 16, 16⟩ : Region) (below σ.sp 80) := by
    have h1 := below_below σ.sp offset 16
    have h2 := below_sub (sp := σ.sp) (a := 16 + offset) (b := 80) (by omega) (by decide)
    rw [hsp]
    exact fun a ha => h2 a (h1 a ha)
  have hf : Frame [⟨s.sp - 16, 16⟩] s.mem (pushState r s).mem :=
    Frame.write (r := ⟨s.sp - 16, 16⟩) (Frame.refl _ _) (by simp) _ (by simp [Region.Contains])
  exact MlKem.bytesAt_frame hf (fun R hR => by
    simp only [List.mem_singleton] at hR
    subst R
    exact (h.si.sub_left hs).symm) (by omega)

theorem inner_source {bytes count : Nat} {σ : State} (h : EntryPre bytes count σ)
    (hb : bytes < 2 ^ 32) :
    VG.Spec.Sha3.bytesAt (innerState σ).mem (σ.gpr .x0) bytes =
      VG.Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) bytes := by
  unfold innerState
  rw [push_source h hb (offset := 48) (by decide) (by simp only [pushState, BitVec.sub_sub]; rfl)]
  rw [push_source h hb (offset := 32) (by decide) (by simp only [pushState, BitVec.sub_sub]; rfl)]
  rw [push_source h hb (offset := 16) (by decide) rfl]
  exact push_source (s := σ) h hb (offset := 0) (by decide) (by simp) .x25

theorem setup_ok (s : State) :
    WP isa (.block [.addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0,
      .addImm .x .x28 .x2 0]) s fun t =>
      VG.Proof.MlKem.AArch64.Only [.x25, .x26, .x28] s t ∧
      t.gpr .x25 = s.gpr .x0 ∧ t.gpr .x26 = s.gpr .x1 ∧ t.gpr .x28 = s.gpr .x2 := by
  open VG.Proof.MlKem.AArch64 in
  refine wp_addImm (by decide) fun a ha h25 =>
    wp_addImm (by decide) fun b hb h26 =>
    wp_addImm (by decide) fun t ht h28 => wp_nil ?_
  refine ⟨((ha.trans hb).trans ht).mono (by simp), ?_, ?_, ?_⟩
  · rw [ht.get .x25, hb.get .x25, h25, BitVec.add_zero]
  · rw [ht.get .x26, h26, BitVec.add_zero, ha.get .x1]
  · rw [h28, BitVec.add_zero, hb.get .x2, ha.get .x2]

end VG.Proof.MlDsa.AArch64.PreparedKey
