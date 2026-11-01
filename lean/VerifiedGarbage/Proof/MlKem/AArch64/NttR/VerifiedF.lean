module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdF
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.AbiF
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.MlKem.Ntt16Contract
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdF
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.AbiF
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.MlKem.Ntt16Contract
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import Init.Data.List.BasicAux
meta import Init.Data.List.BasicAux
public import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact
public import Init.Data.List.BasicAux
meta import Init.Data.List.BasicAux
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
public import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# ML-KEM on AArch64: `vg_mlkem16_ntt` (mlkem-native's schedule) meets its contract

`fwdFast`, with its table of zetas a constant, meets `ntt16Contract`:
correct (`fwdF_run`, `fwdFast_abi`), constant-time, and its precondition
satisfiable.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Impl.MlKem.AArch64.Ntt16.Fast
open VG.Proof.MlKem.AArch64.Ntt16 (hw4)

/-- The contract, with the table a constant. -/
abbrev fastContract : Contract isa := ntt16Contract (abi.withConsts tables)

theorem tables_eq : tables = [(name, tabWords)] := rfl

theorem inF_of_pre {s : State} (h : fastContract.pre s) : InF s := by
  sig_pre [ntt16Contract, inPlace16Contract, inPlace16Sig, AArch64.abi, AArch64.argRegs, tables_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  rw [tabWords_length] at h
  obtain ⟨hd, held, fit, hdw, -, ht, hw, hdis, -, -, red⟩ := h
  have hw0 : (⟨s.gpr .x0, 512⟩ : Region) ∈ s.wr := by rw [hw]; exact List.mem_cons_self
  refine ⟨hw0, red, fun j hj => by rw [held j (by omega), tabWords_get j hj], ?_, (hdw _ hw0).symm⟩
  apply Covers.of_mem
  intro q hq
  rw [List.mem_singleton.mp hq]
  apply List.mem_append_left
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
  simp

theorem fast_correct (s : State) (h : fastContract.pre s) :
    ∃ t s', Exec isa fwdFast s t s' ∧ abiPreserved s s' ∧ fastContract.post s s' := by
  obtain ⟨t, s', he, -, hp⟩ := fwdF_run s (inF_of_pre h)
  refine ⟨t, s', he, fwdFast_abi he, ?_⟩
  sig_post [ntt16Contract, inPlace16Contract, inPlace16Sig, AArch64.abi, AArch64.argRegs, tables_eq,
    Abi.withConsts]
  exact hp

theorem fast_ct : ConstantTime isa fastContract.pre fastContract.pub fwdFast := by
  have hp : ∀ s t, fastContract.pre s → fastContract.pre t → fastContract.pub s t →
      VG.AArch64.Taint.AgreeS [name] (VG.AArch64.Taint.ofRegs [.x0, .x1]) s t := by
    intro s t _ _ h
    sig_pub [ntt16Contract, inPlace16Contract, inPlace16Sig, AArch64.abi, AArch64.argRegs, tables_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1⟩ := h
    refine ⟨agree_of hsp ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h0
      · exact h1
    · intro n hn
      rw [List.mem_singleton.mp hn]
      exact hsy
  exact VG.Taint.constantTime (A := taintS [name]) (VG.AArch64.Taint.ofRegs [.x0, .x1]) hp (by taint_decide)

/-- The memory of the contract's witness: the table at `0x10000`. -/
@[irreducible] def satMem : Mem := constMem 0x10000 tabWords

theorem satMem_held : ∀ i < tabWords.length,
    satMem.readW (0x10000 + BitVec.ofNat 64 (8 * i)) 64 = tabWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [tabWords_length]; omega)

theorem satMem_low {a : Addr} (ha : a.toNat < 0x10000) : satMem a = 0 := by
  unfold satMem constMem
  split
  · rename_i h
    rw [tabWords_length, BitVec.toNat_sub] at h
    have : (0x10000 : Addr).toNat = 0x10000 := rfl
    rw [this] at h
    omega
  · rfl

theorem read_zero (a : Addr) : ∀ n, Mem.read (fun _ => 0) a n = 0
  | 0 => rfl
  | n + 1 => by
    rw [Mem.read, read_zero (a + 1) n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    have (w : Nat) : (0 : BitVec w).toNat = 0 := BitVec.toNat_zero
    rw [this, this, this]
    rfl

theorem satMem_reduced : ReducedW 16 satMem 0x1000 := fun i hi => by
  have hi' : i < 256 := hi
  unfold coeffAtW
  rw [Mem.readW_congr (m' := fun _ => 0) fun k hk => satMem_low (by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : (0x1000 : Addr).toNat = 0x1000 := rfl
    rw [this]; omega), Mem.readW, read_zero]
  decide

/-- The contract's precondition, from its facts. -/
theorem fast_pre {s : State} (hrd : s.rd = [⟨s.syms name, 928⟩])
    (hw : s.wr = [⟨s.gpr .x0, 512⟩, ⟨s.gpr .x1, 512⟩])
    (hdis : (⟨s.gpr .x0, 512⟩ : Region).Disjoint ⟨s.gpr .x1, 512⟩)
    (f0 : (s.gpr .x0).toNat + 512 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 512 ≤ 2 ^ 64)
    (red : ReducedW 16 s.mem (s.gpr .x0))
    (held : ∀ i < tabWords.length, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * i)) 64 = tabWords.getD i 0)
    (fitT : (s.syms name).toNat + 928 ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, (⟨s.syms name, 928⟩ : Region).Disjoint r) (hal : (s.syms name).toNat % 64 = 0) :
    fastContract.pre s := by
  sig_pre [ntt16Contract, inPlace16Contract, inPlace16Sig, AArch64.abi, AArch64.argRegs, tables_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  rw [tabWords_length]
  exact ⟨by rw [hrd]; rfl, fun i hi => held i (by rw [tabWords_length]; exact hi), fitT, hdw, hal,
    by rw [hrd]; rfl, hw, hdis, f0, f1, red⟩

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x10000, 928⟩]
  wr := [⟨0x1000, 512⟩, ⟨0x2000, 512⟩]
  syms _ := 0x10000

theorem fast_sat : ∃ s, fastContract.pre s :=
  ⟨satState, fast_pre rfl rfl (Region.disjoint_of_sep (by decide)) (by decide) (by decide) satMem_reduced
    satMem_held (by decide) (fun r hr => by
      simp only [satState, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)) (by decide)⟩

theorem fast_verified : Verified target fwdFast fastContract :=
  Verified.of_correct fast_correct fast_ct (Contract.Implies.refl fast_sat)

end VG.Proof.MlKem.AArch64.NttR
