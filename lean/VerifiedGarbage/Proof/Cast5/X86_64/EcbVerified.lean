import VerifiedGarbage.Proof.Cast5.X86_64.Ecb
import VerifiedGarbage.Proof.Cast5.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Spec.Cast5.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# CAST5 ECB on x86-64: verified against the shared contracts
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts keyConsts)

/-- The contract the proofs of the ECB functions are written against. -/
def ecbX (d : Spec.Cast5.Direction) : Contract isa where
  pre s := EPre s
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (s.gpr .rdi)) (s.gpr .rsi).toNat d
        (Spec.Cast5.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

theorem ecb_correct (d : Spec.Cast5.Direction) {blk : Prog isa}
    {f : Spec.Cast5.Schedule → Nat → Spec.Cast5.Block → Spec.Cast5.Block}
    (hblk : ∀ u k n, BPre u k n → WP isa blk u (BPost u (f k n (Spec.Cast5.blockAt u.mem (u.gpr .rdx)))))
    (hf : ∀ k n xs, Spec.Cast5.ecb k n d xs = xs.map (f k n))
    (hmx : (ecb blk).allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (h : (ecbX d).pre s) :
    ∃ t s', Exec isa (ecb blk) s t s' ∧ abiPreserved s s' ∧ (ecbX d).post s s' := by
  obtain ⟨t, s', he, hpost, hg⟩ := ecb_ok hblk s h
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, by show _ = _; rw [hpost, hf]⟩

/-- The public registers and the table's address agree. -/
def ecbPub : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8]

theorem ecb_agree (d : Spec.Cast5.Direction) (s₁ s₂ : State) (_ : (ecbX d).pre s₁) (_ : (ecbX d).pre s₂)
    (h : (ecbX d).pub s₁ s₂) : VG.X86_64.Taint.AgreeS [s1234Sym] (Taint.ofRegs ecbPub) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsy⟩ := h
  refine ⟨Taint.agree_ofRegs fun r hr => ?_, fun n hn => ?_⟩
  · simp only [ecbPub, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · simp only [List.mem_singleton] at hn
    subst hn
    exact hsy

theorem ecbEncrypt_ct : ConstantTime isa (ecbX .encrypt).pre (ecbX .encrypt).pub ecbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs ecbPub) (ecb_agree .encrypt)
    (by taint_decide)

theorem ecbDecrypt_ct : ConstantTime isa (ecbX .decrypt).pre (ecbX .decrypt).pub ecbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs ecbPub) (ecb_agree .decrypt)
    (by taint_decide)

theorem ecbConsts_eq : ecbConsts = [(s1234Sym, s1234)] := rfl

/-- The memory of the contracts' witness: the table at `0x100000` (irreducible:
unfolding it in a definitional check would evaluate the table). -/
@[irreducible] def ecbSatMem : Mem := constMem 0x100000 s1234

theorem ecbSatMem_held : ∀ i < 512,
    ecbSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  unfold ecbSatMem
  intro i hi
  exact constMem_held _ _ (by rw [s1234_length]; decide) i (by rw [s1234_length]; exact hi)

/-- A state satisfying the ECB functions' precondition: 16 rounds, one block. -/
def ecbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem EPre.spec_pre (d : Spec.Cast5.Direction) {s : State} (h : EPre s)
    (dTsp : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .rsp, 8⟩)
    (dspK : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 128⟩) :
    (Spec.Cast5.ecbContract (X86_64.abi.withConsts ecbConsts) d).pre s := by
  sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, X86_64.abi, X86_64.argRegs,
    ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  refine ⟨by rw [h.rd]; rfl, h.held, h.fitT, fun r hr => ?_, dTsp, by rw [h.rd]; rfl, h.wr, h.dKD, h.dKS,
    h.dDS, dspK, h.dspD, h.dspS, h.fK, h.fD, h.fS, h.rounds⟩
  rw [h.wr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.dTD
  · exact h.dTS

theorem ecb_implies (d : Spec.Cast5.Direction) :
    (ecbX d).Implies (Spec.Cast5.ecbContract (X86_64.abi.withConsts ecbConsts) d) where
  pre s h := by
    sig_pre [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPre, X86_64.abi, X86_64.argRegs,
      ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, htk, hw, dKD, dKS, dDS, -, spD, spS, fK, fD, fS, hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self), dKD, dKS, dDS, spD, spS, fK, fD,
      fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ h := by
    sig_post [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, Spec.Cast5.ecbPost, X86_64.abi, X86_64.argRegs,
      ecbConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.Cast5.ecbContract, Spec.Cast5.ecbSig, X86_64.abi, X86_64.argRegs, ecbConsts_eq,
      Abi.withConsts] at h
    obtain ⟨-, hsy, h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, h2, h3, h4, h5, hsy⟩
  sat := ⟨ecbSat, EPre.spec_pre d ⟨rfl, rfl, ecbSatMem_held, by decide, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide⟩
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))⟩

theorem ecbEncrypt_verified :
    Verified X86_64.target ecbEncrypt (Spec.Cast5.ecbEncryptContract (X86_64.abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecb_correct .encrypt (fun _ _ _ h => encryptBlock_ok h) (fun _ _ _ => rfl)
    (by lit_decide)) ecbEncrypt_ct (ecb_implies .encrypt)

theorem ecbDecrypt_verified :
    Verified X86_64.target ecbDecrypt (Spec.Cast5.ecbDecryptContract (X86_64.abi.withConsts ecbConsts)) :=
  Verified.of_correct (ecb_correct .decrypt (fun _ _ _ h => decryptBlock_ok h) (fun _ _ _ => rfl)
    (by lit_decide)) ecbDecrypt_ct (ecb_implies .decrypt)

end VG.Proof.Cast5.X86_64
