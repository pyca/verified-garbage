module

import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitErase
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.P384.Prime
import VerifiedGarbage.Proof.P384.Order
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitErase
meta import VerifiedGarbage.Proof.P384.Point
meta import VerifiedGarbage.Proof.P384.Prime
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.TCB.Sig
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P384.Comb7Shape
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.TCB.Sig
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.P384.Comb7Shape
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ecdsa.X86_64.P384.Tables`, which this module and modules that import it used -/

section

/-!
# ECDSA over P-384 on x86-64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `VG_P384_COMB`, not wrapping
around, and apart from the writable regions and the return address; their
length (`p384W_length`, from the tables' shape alone); and a memory holding
them, for the contracts' witnesses (`satMem`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P384

open VG VG.X86_64
open VG.Impl.Ecdsa.X86_64 (p384 CombData)

/-- P-384's comb. -/
abbrev p384d : CombData := ⟨7, Impl.P384.p384Comb7, Impl.P384.p384Comb7Start, "VG_P384_COMB", true, true⟩

/-- The words of P-384's tables. -/
abbrev p384W : List (BitVec 64) := p384.combWords p384d

theorem p384_combConsts : p384.combConsts = [("VG_P384_COMB", p384W)] := rfl

/-- The comb's tables at the static `VG_P384_COMB`, held, not wrapping around,
and apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p384W.length, s.mem.readW (s.syms "VG_P384_COMB" + BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0) ∧
  (s.syms "VG_P384_COMB").toNat + 8 * p384W.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms "VG_P384_COMB", 8 * p384W.length⟩ r

theorem p384_tbl_len : Impl.P384.p384Comb7.length = 55 :=
  Proof.P384.p384Comb7_length

theorem p384_tbl_lenH : ∀ j < 55, (Impl.P384.p384Comb7.getD j []).length = 64 :=
  Proof.P384.p384Comb7_rows

/-- `p384W` has `55 · 64 · 12` words. -/
theorem p384W_length : p384W.length = 42240 :=
  (Proof.Weierstrass.tcombWords_length (n := p384.n) (R := p384.R) (p := p384.C.p)
    (H := 64) (tbl := Impl.P384.p384Comb7) p384_tbl_len p384_tbl_lenH).trans rfl

theorem constRegions_single (f : String → BitVec 64) (n : String) (w : List (BitVec 64)) :
    Abi.constRegions f [(n, w)] = [⟨f n, 8 * w.length⟩] := rfl

/-- The tables' region, `8 · 42240` bytes at the static's address. The proofs
rewrite with this rather than unfold `Abi.constRegions`: the kernel evaluates
closed arithmetic such as `8 * p384W.length` when it compares two forms of
it, which would build the tables' 42240 words. -/
theorem p384_constRegions (f : String → BitVec 64) :
    Abi.constRegions f [("VG_P384_COMB", p384W)] = [⟨f "VG_P384_COMB", 337920⟩] := by
  rw [constRegions_single, p384W_length]

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p384W

theorem satMem_held : ∀ i < p384W.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p384W_length]; omega_using [])

end VG.Proof.Ecdsa.X86_64.P384

end

end

/-! ### `Ecdsa.X86_64.P384.Contract`, which this module and modules that import it used -/

section

/-!
# ECDSA over P-384 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p384.combConsts`),
by name: `vg_ecdsa_p384_sign(out = rdi, d = rsi, digest = rdx, k = rcx,
scratch = r8)`, the result in `eax`, and the tables at the address of the
static `VG_P384_COMB`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P384

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (p384)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P384.curve (ofBytes (bytesAt m d 48)) (hashToInt Spec.P384.curve (bytesAt m digest 48))
    (ofBytes (bytesAt m k 48))

def signX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 96⟩
    let d : Region := ⟨s.gpr .rsi, 48⟩
    let digest : Region := ⟨s.gpr .rdx, 48⟩
    let k : Region := ⟨s.gpr .rcx, 48⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k, ⟨s.syms "VG_P384_COMB", 8 * p384W.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 96 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch, ret]
  post s s' :=
    match sig s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 96 = encode Spec.P384.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 96 = List.replicate 96 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.syms "VG_P384_COMB" = s₂.syms "VG_P384_COMB"

end VG.Proof.Ecdsa.X86_64.P384

end

end

/-!
# ECDSA over P-384 on x86-64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P384.law`, `Proof.P384.combOk7` and the
variant's `inv`), so `sign_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `out` or `scratch`, which the return address
is apart from (`abiPreserved`). Constant time by taint tracking with the
address of the comb's static public (`taintSym`): the only branches are on
loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P384

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p384_nBits : 64 * p384.n ≤ Spec.Ecdsa.nBits p384.C := by
  show 384 ≤ Spec.P384.curve.n.log2 + 1
  have : 383 ≤ Spec.P384.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega_using [this]

/-- No bit of a hash of `48` bytes is dropped. -/
theorem p384_sh : p384.sh = 0 := by
  have h : 64 * 6 ≤ Spec.Ecdsa.nBits p384.C := p384_nBits
  show 8 * 48 - Spec.Ecdsa.nBits p384.C = 0; omega_using [h]

theorem p384_ok (hI : InvSounds) : CfgOk p384 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P384.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask h := absurd h (by decide)
  sh := by rw [p384_sh]; decide
  comb d h := by cases h; exact ⟨by decide, by decide, by decide⟩
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P384.curve.p
    rw [show Spec.P384.curve.p =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
      by decide +kernel]
    exact Proof.P384.prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ p384.C.n_ne_zero Proof.P384.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun _ => by unfold AM3; decide +kernel
  comb_am3 := fun _ _ => by unfold AM3; decide +kernel
  am3 := by unfold AM3; decide +kernel
  even _ := by decide
  inverse _ := ⟨by decide, rfl⟩

theorem p384_tbls (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    CombTbls p384 := fun d h => by cases h; exact ⟨hT, fun _ => Proof.P384.booth hL rfl rfl⟩

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p384_combConsts, show p384.C.len = 48 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, ?_⟩
  rw [TblsHeld, p384_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

/-- `[k]G` is a call of `vg_p384_mul_base`, which calls no other function. -/
theorem p384_mulBase : MulBaseOk p384 :=
  ⟨fun _ => ⟨_, rfl, by decide, by lit_decide⟩, fun h => absurd h (by decide)⟩

/-- The inlining checks, shared by correctness and the two call wrappers. -/
theorem sign_inlineOk : signP384.InlineOk = true := by lit_decide

theorem sign_x86 (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP384.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p384_ok hI) hL (p384_tbls hL hT) (pre_of hs) p384_mulBase
  have hok := sign_inlineOk
  have hsp := Code.clobbers_rsp_of_inlineOk hok
  have hmx : signP384.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
    rw [Code.allInstrs_inline]; lit_decide
  have F := (Exec.regions he (Code.noCalls_inline hok)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
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

/-- Constant time by taint tracking, which follows the calls: `rsp` is
public, as the return addresses they store are. -/
theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signP384 :=
  VG.Taint.constantTime_mapBlocks (c' := signErased) (taintSym_eraseInv ["VG_P384_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

/-- The output is apart from the calls' return address. -/
theorem post_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : signX86_64.post s b) :
    signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := 96) (by rw [hs.2.1]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

/-- The function with its calls, for a caller (RFC 6979's) that keeps its
buffers off the 8 bytes below `rsp`. -/
theorem sign_call_x86 (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) (s : State) (hs : signX86_64.pre s) (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signP384 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) sign_inlineOk (sign_x86 hL hT hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

end VG.Proof.Ecdsa.X86_64.P384
