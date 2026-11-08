module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyCT
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyFn
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Verify
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_ed25519_verify_equation` on PPC64LE, by register

The function meets a contract of its facts by register (`verifyPPC`), with
no stack, and the static of the cached `-[1]B … -[15]B` (`bSym`, `bWord`):
the callers in this library call it through it. It saves and restores the
nonvolatile registers it writes, and `lr`, which its calls and `adrSym`
overwrite (`verify_ok'`), given the windows' proof (`RhsOk`). The contract
declares the inputs and the static's address public, and two runs on the
same inputs leak the same trace (`verifyEquation_rel`, `verify_ct`), given
the windows' constant time (`RhsCT`). What a caller's contract under
`abi.withConsts bConsts` says of the static: `bstat_of_consts`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE

/-- `vg_ed25519_verify_equation`'s contract by register, an internal function's. -/
def verifyPPC : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 32⟩
    let sig : Region := ⟨s.gpr .r4, 64⟩
    let ch : Region := ⟨s.gpr .r5, 64⟩
    let ws : Region := ⟨s.gpr .r6, 8192⟩
    let tb : Region := ⟨s.syms bSym, 1920⟩
    s.rd = [pk, sig, ch, tb] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws ∧
      (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧ tb.Disjoint ws
  post s s' := (s'.gpr .r3).setWidth 32 = if Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .r3) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .r4) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .r5) 64) then 1 else 0
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r3) 32 ++ Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r4) 64 ++
      Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r5) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r3) 32 ++ Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r4) 64 ++
      Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r5) 64).map (·.toNat) ∧ s₁.syms bSym = s₂.syms bSym

theorem verifyPPC_pre {s : State} (hs : verifyPPC.pre s) : VerifyPre s :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  ⟨h1, h2, h3, h4, h5, ⟨by rw [h1]; simp, h6, h7, h8⟩⟩

theorem verify_ok' (hR : RhsOk) (s : State) (hs : verifyPPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.PPC64LE.verifyEquation s t s' ∧ abiPreserved s s' ∧
      verifyPPC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hlr, hr⟩ := verify_ok hR (verifyPPC_pre hs)
  refine ⟨t, s', he, ⟨hg, hsp, hlr⟩, ?_⟩
  show (s'.gpr .r3).setWidth 32 = _
  rw [hr]
  split <;> rfl

theorem bytes_of_leak {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  have e : a₁ ++ b₁ ++ c₁ = a₂ ++ b₂ ++ c₂ := by
    have := congrArg (List.map fun n => BitVec.ofNat 8 n) h
    simpa [List.map_map, Function.comp_def] using this
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

theorem verify_ct (hR : RhsOk) (hRC : RhsCT) :
    ConstantTime isa verifyPPC.pre verifyPPC.pub Impl.Ed25519.PPC64LE.verifyEquation := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨p3, p4, p5, p6, psp, pl, psy⟩ := hp
  have hl : ∀ (s : State) (p : Addr) (n : Nat), (Spec.Ed25519.bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [Spec.Ed25519.bytesAt]
  obtain ⟨b3, b4, b5⟩ := bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl]) pl
  refine verifyEquation_rel hR hRC (b := s₁.gpr .r6) (sp := s₁.sp) (pk := s₁.gpr .r3) (sig := s₁.gpr .r4)
    (ch := s₁.gpr .r5) (T := s₁.syms bSym) (PK := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r3) 32)
    (SG := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r4) 64) (CH := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r5) 64)
    _ _ _ _ _ _ ⟨⟨verifyPPC_pre h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨verifyPPC_pre h₂, psy.symm, p3.symm, p4.symm, p5.symm, p6.symm, psp.symm, by rw [b3, p3], by rw [b4, p4],
        by rw [b5, p5]⟩⟩ e₁ e₂

theorem bWords_length : bWords.length = 240 := by simp [bWords]

theorem bWords_getD {q : Nat} (hq : q < 240) : bWords.getD q 0 = bWord q := by
  simp [bWords, hq]

/-- What `abi.withConsts [(bSym, ws)]` says of the static, for words `ws` of `bWord`. -/
theorem bstat_of_consts' {st : Nat} {s : State} {ws : List (BitVec 64)} (hl : ws.length = 240)
    (hg : ∀ q < 240, ws.getD q 0 = bWord q) (h : ConstsOk [(bSym, ws)] st s) :
    (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 1920⟩ r := by
  have hrd := h.mem_rd List.mem_cons_self
  have hfit := h.fit List.mem_cons_self
  have hd : (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 8 * ws.length⟩ r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 8 * ws.length⟩ r :=
    (h.2.2.1 _ List.mem_cons_self).2
  rw [hl] at hrd hfit hd
  refine ⟨hrd, hfit, fun q hq => ?_, hd.1, hd.2⟩
  rw [h.readW List.mem_cons_self (by rw [hl]; exact hq), hg q hq]

/-- What `abi.withConsts bConsts` says of the static. -/
theorem bstat_of_consts {st : Nat} {s : State} (h : ConstsOk bConsts st s) :
    (⟨s.syms bSym, 1920⟩ : Region) ∈ s.rd ∧ (s.syms bSym).toNat + 1920 ≤ 2 ^ 64 ∧
      (∀ q < 240, s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * q)) 64 = bWord q) ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨s.syms bSym, 1920⟩ r) ∧
      ∀ r ∈ PPC64LE.abi.reserved st s, Region.Disjoint ⟨s.syms bSym, 1920⟩ r :=
  bstat_of_consts' bWords_length (fun _ hq => bWords_getD hq) h

/-- The readable regions under `abi.withConsts [(bSym, ws)]`: those without it, then the static. -/
theorem rd_of_bconsts' {st : Nat} {s : State} {ws : List (BitVec 64)} {L : List Region}
    (hl : ws.length = 240) (h : ConstsOk [(bSym, ws)] st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [⟨s.syms bSym, 1920⟩] := by
  have h1 := h.1
  simp only [List.length_singleton, constRegs, Abi.constRegions, List.map_cons, List.map_nil, hl] at h1
  calc s.rd = s.rd.take (s.rd.length - 1) ++ s.rd.drop (s.rd.length - 1) := (List.take_append_drop _ _).symm
    _ = L ++ [⟨s.syms bSym, 1920⟩] := by rw [hL, h1]

theorem rd_of_bconsts {st : Nat} {s : State} {L : List Region} (h : ConstsOk bConsts st s)
    (hL : s.rd.take (s.rd.length - 1) = L) : s.rd = L ++ [⟨s.syms bSym, 1920⟩] :=
  rd_of_bconsts' bWords_length h hL

end VG.Proof.Ed25519.PPC64LE
