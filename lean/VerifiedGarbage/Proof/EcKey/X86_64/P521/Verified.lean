module

public import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.P521.X86_64.TaintSums
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
public import VerifiedGarbage.Impl.EcKey.P521.X86_64
import VerifiedGarbage.Proof.Framework.LitShare
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
meta import VerifiedGarbage.Proof.EcKey.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
meta import VerifiedGarbage.Proof.P521.X86_64.TaintSums
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
meta import VerifiedGarbage.Impl.EcKey.P521.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import Batteries.Data.List.Lemmas
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
public import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Tables
meta import VerifiedGarbage.Spec.EcKey.P521
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Tables

/-! ### `EcKey.X86_64.P521.Contract`, which this module and modules that import it used -/

section

/-!
# P-521 public keys on x86-64: the contract the proof is written against

The facts of `Spec.EcKey.P521.inst.publicKeyContract` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p521.combConsts`),
by name: `vg_ec_p521_public_key(out = rdi, d = rsi, scratch = rdx)`, the
result in `eax`, and the tables at the address of the static
`VG_P521_COMB`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.P521

open VG VG.X86_64 Spec.Weierstrass Spec.EcKey
open VG.Impl.Ecdsa.X86_64 (p521)
open VG.Proof.Ecdsa.X86_64.P521 (TblHeld p521W p521_constRegions p521_combConsts satMem satMem_held)

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P521.curve) :=
  publicKey Spec.P521.curve (ofBytes (bytesAt m d 66))

def pkX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 133⟩
    let d : Region := ⟨s.gpr .rsi, 66⟩
    let scratch : Region := ⟨s.gpr .rdx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, ⟨s.syms "VG_P521_COMB", 764928⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 133 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch, ret]
  post s s' :=
    match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 133 = encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 133 = List.replicate 133 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.syms "VG_P521_COMB" = s₂.syms "VG_P521_COMB"

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
  rd := [⟨0x2000, 66⟩, ⟨0x100000, 764928⟩]
  wr := [⟨0x1000, 133⟩, ⟨0x8000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 66⟩, ⟨s.syms "VG_P521_COMB", 764928⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 133⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 133⟩ ⟨s.gpr .rsi, 66⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 133⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 66⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 133⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 66⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 133 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 66 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblHeld s [⟨s.gpr .rdi, 133⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms "VG_P521_COMB").toNat % 64 = 0) :
    (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts)).pre s := by
  sig_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
    X86_64.argRegs, p521_combConsts, Abi.withConsts, p521_constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, f0, f1, f2⟩

theorem sat_spec : (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts)).pre
    satState := by
  have held : ∀ i < p521W.length, satState.mem.readW (satState.syms "VG_P521_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p521W.getD i 0 := satMem_held
  refine spec_pre rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) (by decide) ⟨held, ?_, ?_⟩ (by decide)
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    pkX86_64.Implies (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts)) where
  pre s h := by
    sig_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p521_combConsts, Abi.withConsts, p521_constRegions, Abi.constsHeld, stackBelow] at h
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
    sig_post [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p521_combConsts, Abi.withConsts, pkX86_64, pk]
    simp only [pkX86_64, pk, Spec.P521.curve] at h
    revert h
    generalize publicKey _ _ = q
    rcases q with _ | _ | ⟨x, y⟩ <;> exact id
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, p521_combConsts, Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hs⟩
  sat := ⟨satState, sat_spec⟩

end VG.Proof.EcKey.X86_64.P521

end

end

/-!
# P-521 public keys on x86-64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the registration
file supplies: `Proof.P521.law`, `Proof.P521.combOk7` and the variant's
`inv`), so `publicKey_ok` gives the
contract's postcondition; the callee-saved registers are restored, `rsp` is
never written, and every store is to `out` or `scratch`, which the return
address is apart from (`abiPreserved`). Constant time by taint tracking with
the address of the comb's static public (`taintSym`): the only branches are
on loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P521

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p521_combConsts, p521_constRegions, show p521.C.len = 66 from rfl]; simp only [
    List.cons_append, List.nil_append], h2, h3, h4, h5, h8, h9, ?_⟩
  rw [TblsHeld, p521_combConsts]
  refine ⟨fun c hc => ?_, fun t ht => ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · simp only [p521_constRegions, List.mem_singleton] at ht; subst ht
    refine ⟨fit, fun r hr => hdw r ?_⟩
    rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

theorem post_of {s s' : State} (h : PkPost p521 s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  dsimp only [pkX86_64]
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey p521.C (dk p521 s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- `publicKeyP521` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its checks of every instruction evaluate
(`Proof/Weierstrass/X86_64/CodeErase.lean`). -/
def publicKeyP521Erased : Prog isa := Code.erase publicKeyP521

materialize_shared publicKeyP521Erased

/-- `InlineOk`, checked once for every theorem that needs it. -/
theorem pk_inlineOk : publicKeyP521.InlineOk = true := by
  rw [← Code.InlineOk_erase]
  show publicKeyP521Erased.InlineOk = true
  lit_decide

theorem pk_x86 (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyP521.inline s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (c := p521) (p521_ok hI).toBaseCfgOk hL (p521_tbls hT) (pre_of hs)
  have hsp := Code.clobbers_rsp_of_inlineOk pk_inlineOk
  have F := (Exec.regions he (Code.noCalls_inline pk_inlineOk)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by
    rw [Code.allInstrs_inline, ← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [loadsMxcsr_erase]]
    show publicKeyP521Erased.allInstrs _ = true
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

theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyP521 := by
  obtain ⟨_, hc⟩ : ∃ h, ((taintSym ["VG_P521_COMB"]).check
      (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) publicKeyP521 h).isSome = true := by
    taint_decide_sum [Proof.P521.X86_64.combGSum, Proof.P521.X86_64.invPSum]
  refine VG.Taint.constantTime (A := taintSym ["VG_P521_COMB"]) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ hc
  exact fun _ _ _ _ ⟨h0, h1, h2, h3, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩

theorem sat_spec8 :
    (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 8).pre satState := by
  have held : ∀ i < p521W.length, satState.mem.readW (satState.syms "VG_P521_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p521W.getD i 0 := satMem_held
  sig_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
    X86_64.argRegs, p521_combConsts, Abi.withConsts, p521_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    pkX86_64.Implies (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 8) :=
  implies.stack8 ⟨satState, sat_spec8⟩

/-- The output is apart from the calls' return address. -/
theorem pk_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 8).pre s)
    (hp : pkX86_64.post s b) : pkX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre_consts hs) (p := s.gpr .rdi) (n := 133)
    (by rw [hwr]; simp) (by decide)
  simpa only [pkX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem pk_verified (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyP521
      (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts p521.combConsts) 8) :=
  Verified.of_inline_ct pk_inlineOk (pk_x86 hL hT hI) pk_ct implies8
    (fun _ h => Sig.clear_of_pre_consts h) pk_patch

end VG.Proof.EcKey.X86_64.P521
