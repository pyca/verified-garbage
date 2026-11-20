module

public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Proof.EcKey.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
import VerifiedGarbage.Proof.EcKey.X86_64.P224.Lit
public import VerifiedGarbage.Impl.EcKey.P224.X86_64
import VerifiedGarbage.Proof.Framework.LitShare
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.EcKey.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
meta import VerifiedGarbage.Proof.EcKey.X86_64.P224.Lit
meta import VerifiedGarbage.Impl.EcKey.P224.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import Batteries.Data.List.Lemmas
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `EcKey.X86_64.P224.Contract`, which only this module used -/

section

/-!
# P-224 public keys on x86-64: the contract the proof is written against

The facts of `Spec.EcKey.P224.inst.publicKeyContract` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p224.combConsts`),
by name: `vg_ec_p224_public_key(out = rdi, d = rsi, scratch = rdx)`, the
result in `eax`, and the tables at the address of the static
`VG_P224_COMB`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.P224

open VG VG.X86_64 Spec.Weierstrass Spec.EcKey
open VG.Impl.Ecdsa.X86_64 (p224)
open VG.Proof.Ecdsa.X86_64.P224 (TblHeld p224W p224W_length p224_combConsts satMem satMem_held)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P224.curve) :=
  publicKey Spec.P224.curve (ofBytes (bytesAt m d 28))

def pkX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 57⟩
    let d : Region := ⟨s.gpr .rsi, 28⟩
    let scratch : Region := ⟨s.gpr .rdx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, ⟨s.syms "VG_P224_COMB", 8 * p224W.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch, ret]
  post s s' :=
    match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 57 = encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 57 = List.replicate 57 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.syms "VG_P224_COMB" = s₂.syms "VG_P224_COMB"

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 28⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 28⟩, ⟨s.syms "VG_P224_COMB", 8 * p224W.length⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 57⟩ ⟨s.gpr .rsi, 28⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 57⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 28⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 57⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 28⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 57 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 28 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms "VG_P224_COMB").toNat % 64 = 0) :
    (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts)).pre s := by
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
    X86_64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, f0, f1, f2⟩

theorem sat_spec : (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts)).pre
    satState := by
  have hl := p224W_length
  have held : ∀ i < p224W.length, satState.mem.readW (satState.syms "VG_P224_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    pkX86_64.Implies (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts)) where
  pre s h := by
    sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p224_combConsts, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, -, ht, hw, h1, h2, h3, r1, -, r3, f0, -, f2⟩ := h
    refine ⟨?_, hw, h2, h1, h3, r1, r3, f0, f2, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p224_combConsts, Abi.withConsts, pkX86_64, pk]
    simp only [pkX86_64, pk, Spec.P224.curve] at h
    revert h
    generalize publicKey _ _ = q
    rcases q with _ | _ | ⟨x, y⟩ <;> exact id
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p224_combConsts, Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.EcKey.X86_64.P224

end

end

/-!
# P-224 public keys on x86-64: `Verified`

P-224 is a curve the proof supports (`p224_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P224.law`, `Proof.P224.combOk7` and the
variant's `inv`), so `publicKey_ok` gives the
contract's postcondition; the callee-saved registers are restored, `rsp` is
never written, and every store is to `out` or `scratch`, which the return
address is apart from (`abiPreserved`). Constant time by taint tracking with
the address of the comb's static public (`taintSym`): the only branches are
on loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.P224

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p224_combConsts, show p224.C.len = 28 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h8, h9, ?_⟩
  rw [TblsHeld, p224_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

theorem post_of {s s' : State} (h : PkPost p224 s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  dsimp only [pkX86_64]
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey p224.C (dk p224 s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- `publicKeyP224` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def publicKeyP224Erased : Prog isa := Code.erase publicKeyP224

materialize_shared publicKeyP224Erased

theorem pk_inlineOk : publicKeyP224.InlineOk = true := by
  rw [← Code.InlineOk_erase]
  show publicKeyP224Erased.InlineOk = true
  lit_decide

theorem pk_x86 (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP224.inline s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (p224_ok hI) hL (p224_tbls hT) (pre_of hs) p224_mulBase
  have hsp : ∀ i ∈ instrs publicKeyP224.inline, Taint.clobbers i .rsp = false := by
    have h : publicKeyP224.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
      rw [← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [Taint.clobbers_erase]]
      show publicKeyP224Erased.allInstrs _ = true
      lit_decide
    rw [← Code.allInstrs_inline, Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (Code.noCalls_inline pk_inlineOk)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by
    rw [Code.allInstrs_inline, ← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [loadsMxcsr_erase]]
    show publicKeyP224Erased.allInstrs _ = true
    lit_decide) he
    ⟨fun r hr => ?_, ?_⟩, post_of hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)


theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP224 :=
  VG.Taint.constantTime_mapBlocks (c' := publicKeyP224Erased) (taintSym_eraseInv ["VG_P224_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

theorem sat_spec8 :
    (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts) 8).pre satState := by
  have held : ∀ i < p224W.length, satState.mem.readW (satState.syms "VG_P224_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := satMem_held
  sig_pre [Spec.EcKey.P224.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords, X86_64.abi,
    X86_64.argRegs, p224_combConsts, Abi.withConsts, p224_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    pkX86_64.Implies (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts) 8) :=
  implies.stack8 ⟨satState, sat_spec8⟩

/-- The output is apart from the calls' return address. -/
theorem pk_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts) 8).pre s)
    (hp : pkX86_64.post s b) : pkX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre_consts hs) (p := s.gpr .rdi) (n := 57)
    (by rw [hwr]; simp) (by decide)
  simpa only [pkX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem pk_verified (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP224
      (Spec.EcKey.P224.inst.publicKeyContract (X86_64.abi.withConsts p224.combConsts) 8) :=
  Verified.of_inline_ct pk_inlineOk (pk_x86 hL hT hI) pk_ct implies8
    (fun _ h => Sig.clear_of_pre_consts h) pk_patch


theorem publicKey_codeSp : (publicKeyP224).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_ec_p224_public_key` as emitted (`Impl.EcKey.X86_64.Fn.publicKeyP224`), its cleanup included, meets its contract in
constant time and returns without secret residue. -/
theorem publicKey_scrubbed (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    VerifiedScrubbed X86_64.target Impl.EcKey.X86_64.Fn.publicKeyP224
      (Spec.EcKey.P224.publicKeyApi.contract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p224.combConsts) 8) 32 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.P224.publicKeyApi)
    { code := publicKeyP224
      stack := 8
      verified := pk_verified hL hT hI
      spSafe := publicKey_codeSp } .sse (EcKey.X86_64.Scrub.publicKeyOut_consts Spec.EcKey.P224.inst 8 Impl.Ecdsa.X86_64.p224.combConsts)

theorem publicKey_spSafe : Impl.EcKey.X86_64.Fn.publicKeyP224.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe publicKey_codeSp

end VG.Proof.EcKey.X86_64.P224
