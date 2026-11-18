module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64.SealGather
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Gather.RISCV64.Loop
public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
meta import VerifiedGarbage.Proof.Gather.RISCV64.Loop
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64.SealGather
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
meta import VerifiedGarbage.Proof.AesGcm.ScratchGather
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace

/-! ### `ChaCha20Poly1305.RISCV64.Gather.CT`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.RISCV64.Gather.Fn`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.RISCV64.Gather.Contract`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, RISC-V: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_chacha20_poly1305_seal_gather` is written against, which the shared one
(`Spec.ChaCha20Poly1305.sealGatherContract`, with the 640 bytes of stack
below the stack pointer that its frame and its call use) implies
(`Gather/Verified.lean`): `(key = a0, nonce = a1, aad = a2, aad_len = a3,
src = a4, src_count = a5, dst = a6, len = a7, tag)`, `tag` the first
argument in memory (`stackArg s 0`). As on PPC64LE
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Fn.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Gather

open VG VG.RISCV64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)

section
variable (s : State)

/-- The arguments. -/
abbrev K : Addr := s.gpr .a0
abbrev Nn : Addr := s.gpr .a1
abbrev Ad : Addr := s.gpr .a2
abbrev AL : Nat := (s.gpr .a3).toNat
abbrev Src : Addr := s.gpr .a4
abbrev Cnt : Nat := (s.gpr .a5).toNat
abbrev Dst : Addr := s.gpr .a6
abbrev L : Nat := (s.gpr .a7).toNat
abbrev Tg : Addr := stackArg s 0

/-- The regions: the key, the nonce, the additional data, the descriptors,
the slices they list, the output, the tag, the stack argument and the stack
below the stack pointer. -/
abbrev kR : Region := ⟨K s, 32⟩
abbrev nR : Region := ⟨Nn s, 12⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev dsR : Region := ⟨Src s, Cnt s * 16⟩
abbrev lsR : List Region := Sig.listed 64 s.mem .u8 (Src s) (Cnt s)
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tgR : Region := ⟨Tg s, 16⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 8⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 640, 640⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 64 s.mem (Src s) i
abbrev pt (i : Nat) : List Byte := gathered 64 s.mem (Src s) i

end

/-- What the code of `vg_chacha20_poly1305_seal_gather` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] ∧ s.wr = [dR s, tgR s] ∧
    (kR s).Disjoint (dR s) ∧ (kR s).Disjoint (tgR s) ∧ (nR s).Disjoint (dR s) ∧
    (nR s).Disjoint (tgR s) ∧ (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧
    (dsR s).Disjoint (dR s) ∧ (dsR s).Disjoint (tgR s) ∧
    (∀ r ∈ lsR s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s)) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (kR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧ (stkR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧
    (K s).toNat + 32 ≤ 2 ^ 64 ∧ (Nn s).toNat + 12 ≤ 2 ^ 64 ∧ (Ad s).toNat + AL s ≤ 2 ^ 64 ∧
    (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (Dst s).toNat + L s ≤ 2 ^ 64 ∧ (Tg s).toNat + 16 ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 640 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧ gl s (Cnt s) = L s ∧ L s ≤ pMax

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    ∀ i < Cnt s₁ * 16, s₁.mem (Src s₁ + BitVec.ofNat 64 i) = s₂.mem (Src s₁ + BitVec.ofNat 64 i)

/-- What `vg_chacha20_poly1305_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encrypt (bytesAt s.mem (K s) 32) (bytesAt s.mem (Nn s) 12) (bytesAt s.mem (Ad s) (AL s)) (pt s (Cnt s)) =
    (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)

/-- `vg_chacha20_poly1305_seal_gather`. -/
def gatherRISCV64 : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

end VG.Proof.ChaCha20Poly1305.RISCV64.Gather

end

end

/-! ### `ChaCha20Poly1305.RISCV64.Gather.Callee`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, RISC-V: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls `vg_chacha20_poly1305_seal`, with its working space in a frame of its
own, by its shared contract (`Spec.ChaCha20Poly1305.sealContract`, with 624
bytes of stack, which its frame uses: `seal_sdepth`): its precondition from
the layout the call gives it (`callPre`, `sealSpec_pre`), its postcondition
(`sealSpec_post`) and its public data (`sealSpec_pub`). As on PPC64LE
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Callee.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Gather

open VG VG.RISCV64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- The frame of `vg_chacha20_poly1305_seal` uses the 624 bytes of stack its
contract reserves. -/
theorem seal_sdepth : sdepth Impl.ChaCha20Poly1305.RISCV64.SealGather.sealCode = 624 := by
  decide +kernel

/-- What a call of `vg_chacha20_poly1305_seal(key = a0, nonce = a1, aad = a2,
aad_len = a3, data = a4, len = a5, tag = a6)` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .a0, 32⟩
  let nonce : Region := ⟨s.gpr .a1, 12⟩
  let aad : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let data : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let tag : Region := ⟨s.gpr .a6, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 624, 624⟩
  s.rd = [key, nonce, aad] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    (s.gpr .a0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a6).toNat + 16 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 624 ≤ s.sp.toNat

theorem sealSpec_pre {s : State} (h : callPre s) :
    (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, RISCV64.abi, RISCV64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, RISCV64.abi,
    RISCV64.argRegs, List.getD]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).post s s') :
    encrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat, bytesAt s'.mem (s.gpr .a6) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, RISCV64.abi, RISCV64.argRegs] at h
  exact h

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp) :
    (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, RISCV64.abi, RISCV64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, RISCV64.abi, RISCV64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.ChaCha20Poly1305.RISCV64.Gather

end

end


/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, RISC-V: the function

Untrusted: everything here is checked by Lean. With `Bs` the base of the 640
bytes of stack below the stack pointer (`sp = Bs + 640`),
`vg_chacha20_poly1305_seal_gather` pushes its frame of 16 bytes at
`Bs + 624`, which keeps our return address at `Bs + 632`; keeps `tag`, from
the stack above the frame, in `t5` and `dst` in `t6` (`entered_wp`);
gathers the slices to `dst` (`gather_wp`); and calls
`vg_chacha20_poly1305_seal` on them in place, by its contract
(`sealSpec_pre`, `sealSpec_post`), whose frame is in the 624 bytes below
ours, so the return address comes back from it (`sealGather_wp`). As on
PPC64LE (`Proof/ChaCha20Poly1305/PPC64LE/Gather/Fn.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Gather

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.ChaCha20Poly1305.RISCV64.SealGather VG.WriteBytes
open VG.Impl.ChaCha20.RISCV64.Xor (mov)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.Gather.RISCV64 (GatherPre gather_wp gatherRegs)

/-- The correctness of `vg_chacha20_poly1305_seal`, in its frame, by its
shared contract. -/
abbrev SealOk : Prop :=
  ∀ s, (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pre s →
    ∃ t s', Exec isa sealCode s t s' ∧ abiPreserved s s' ∧ (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).post s s'

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  Covers.of_sub fun r hr => ⟨r, h r hr, 0, (BitVec.add_zero _).symm, by omega_arith⟩

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 640 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 640

/-- Our frame, and the return address in it. -/
abbrev FA : Region := ⟨Bs s + BitVec.ofNat 64 624, 16⟩
abbrev raA : Addr := Bs s + BitVec.ofNat 64 632

/-- The memory after the push. -/
abbrev eMem : Mem := s.mem.write (raA s) 8 (s.gpr .ra)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gMem : Mem := writeBytes (eMem s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_chacha20_poly1305_seal` reads and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 640
  hBn : (Bs s).toNat + 648 ≤ 2 ^ 64
  bk : (⟨Bs s, 640⟩ : Region).Disjoint (kR s)
  bn : (⟨Bs s, 640⟩ : Region).Disjoint (nR s)
  ba : (⟨Bs s, 640⟩ : Region).Disjoint (aR s)
  bds : (⟨Bs s, 640⟩ : Region).Disjoint (dsR s)
  bl : ∀ r ∈ lsR s, (⟨Bs s, 640⟩ : Region).Disjoint r
  bd : (⟨Bs s, 640⟩ : Region).Disjoint (dR s)
  bt : (⟨Bs s, 640⟩ : Region).Disjoint (tgR s)
  hargR : argR s = ⟨Bs s + BitVec.ofNat 64 640, 8⟩
  al : s.sp.toNat % 16 = 0
  w₁ : 640 ≤ s.sp.toNat
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, al, w₁, w₂, hgl, hpm⟩ := hs
  have hB : s.sp = Bs s + BitVec.ofNat 64 640 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 648 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega_arith
  refine ⟨⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, al, w₁, w₂, hgl, hpm⟩, hB, hBn, bk, bn, ba, bds, bl, bd, bt, ?_, al, w₁, hgl,
    ods⟩
  show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 8⟩ : Region) = ⟨Bs s + BitVec.ofNat 64 640, 8⟩
  rw [← hB]; simp

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 640) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 640⟩ :=
  Offset.sub_base _ h'

theorem stk_sub0 (s : State) (n : Nat) (h' : n ≤ 640) : (⟨Bs s, n⟩ : Region).Sub ⟨Bs s, 640⟩ :=
  Region.sub_prefix h'

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem fsp : s.sp - 16 = Bs s + BitVec.ofNat 64 624 := by
  rw [h.hB, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, Offset.add_ofNat_sub _ (by decide)]

theorem fra : s.sp - 16 + 8 = raA s := by
  rw [h.fsp, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add]

theorem bs_toNat : (Bs s).toNat = s.sp.toNat - 640 := by
  have e := congrArg BitVec.toNat h.hB
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
  have := h.hBn
  omega_using [e, this]

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

omit h in
/-- The memory the push left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 640⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  Mem.write_apply fun hc => hr x hx (stk_sub s 632 8 (by decide) x (by
    simp only [Region.Contains, raA] at hc ⊢; omega_using [hc]))

theorem frame_eMem : Frame [FA s] s.mem (eMem s) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _
    (Offset.contains (Bs s) (d := 632) (e := 624) (by decide) (by decide) (by have := h.hBn; omega_using []))

/-- `tag`, after the push. -/
theorem eTag : (eMem s).readW (Bs s + BitVec.ofNat 64 640) 64 = Tg s := by
  rw [Frame.readW h.frame_eMem (r := ⟨Bs s + BitVec.ofNat 64 640, 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by decide)) (by have := h.hBn; omega_using []) (by have := h.hBn; omega_using []))
    (by decide)]
  show _ = s.mem.readW (stackArgAddr s 0) 64
  rw [show stackArgAddr s 0 = Bs s + BitVec.ofNat 64 640 from congrArg Region.base h.hargR]

/-- The descriptors and the slices, after the push. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eMem s x := by
  intro r hr x hx
  refine (keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bl r hr).symm

theorem hpt : Spec.Gcm.gathered 64 (eMem s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gMem : Frame [dR s] (eMem s) (gMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- The return address, once the slices are gathered. -/
theorem gRa : (gMem s).read (raA s) 8 = s.gpr .ra := by
  rw [Frame.read h.frame_gMem (r := ⟨raA s, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.bd.sub_left (stk_sub s 632 8 (by decide))) (by decide)]
  exact read_write_self _ _ _

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  a0 : e.gpr .a0 = s.gpr .a0
  a1 : e.gpr .a1 = s.gpr .a1
  a2 : e.gpr .a2 = s.gpr .a2
  a3 : e.gpr .a3 = s.gpr .a3
  a4 : e.gpr .a4 = Src s
  a5 : e.gpr .a5 = s.gpr .a5
  a6 : e.gpr .a6 = Dst s
  a7 : e.gpr .a7 = s.gpr .a7
  t5 : e.gpr .t5 = Tg s
  t6 : e.gpr .t6 = Dst s
  pres : ∀ r ∈ preserved, e.gpr r = s.gpr r
  sp : e.sp = Bs s + BitVec.ofNat 64 624
  rd : e.rd = s.rd
  wr : e.wr = FA s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (pushed .ra s) (Entered s) := by
  have asp : (pushed .ra s).sp = Bs s + BitVec.ofNat 64 624 := h.fsp
  have amem : (pushed .ra s).mem = eMem s := by
    show s.mem.write (s.sp - 16 + 8) 8 (s.gpr .ra) = _
    rw [h.fra]
  have ag (r : Reg) : (pushed .ra s).gpr r = s.gpr r := rfl
  unfold entry
  refine wp_addSp (imm := 16) (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .t5 = Bs s + BitVec.ofNat 64 640 := by rw [v₁.gpr, asp, Offset.add_add]
  refine wp_ld (a := Bs s + BitVec.ofNat 64 640) (by decide) (by rw [p₁]; exact BitVec.add_zero _)
    (by rw [← h.hB]; have := h.al; omega_using [this])
    (by rw [v₁.rd, v₁.wr]
        exact ⟨_, List.mem_append_left _ h.argIn, by rw [h.hargR]; exact Region.contains_self _ _⟩)
    fun u₂ v₂ => wp_mv fun u₃ v₃ => WP.block_nil ?_
  have g (r : Reg) (h5 : r ≠ .t5) (h6 : r ≠ .t6) : u₃.gpr r = s.gpr r := by
    rw [v₃.other r h6, v₂.other r h5, v₁.other r h5, ag]
  have hpres : ∀ r ∈ preserved, r ≠ .t5 ∧ r ≠ .t6 := by decide
  exact ⟨by rw [v₃.mem, v₂.mem, v₁.mem, amem], g _ (by decide) (by decide), g _ (by decide) (by decide),
    g _ (by decide) (by decide), g _ (by decide) (by decide), g _ (by decide) (by decide),
    g _ (by decide) (by decide), g _ (by decide) (by decide), g _ (by decide) (by decide),
    by rw [v₃.other _ (by decide), v₂.gpr, v₁.mem, amem, h.eTag],
    by rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), ag],
    fun r hr => g r (hpres r hr).1 (hpres r hr).2, by rw [v₃.sp, v₂.sp, v₁.sp, asp],
    by rw [v₃.rd, v₂.rd, v₁.rd]; rfl,
    by rw [v₃.wr, v₂.wr, v₁.wr]; show ⟨s.sp - 16, 16⟩ :: s.wr = _; rw [h.fsp]⟩

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, al, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { a4 := he.a4
          a5 := by rw [he.a5, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          a6 := he.a6
          hcnt := (s.gpr .a5).isLt
          dw := ods
          lt := (s.gpr .a7).isLt
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_mem fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact List.mem_append_left _ (by rw [he.rd, rd]; simp)
          lsr := fun r hr => covers_mem fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            rw [hls] at hr
            exact List.mem_append_left _ (by rw [he.rd, rd]; simp [hr])
          dw' := covers_mem fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            rw [he.wr, wr]; simp
          dsd := dsd
          lsd := fun r hr => (lsdt r (by rw [hls] at hr; exact hr)).1 }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gMem s
  a0 : g.gpr .a0 = s.gpr .a0
  a1 : g.gpr .a1 = s.gpr .a1
  a2 : g.gpr .a2 = s.gpr .a2
  a3 : g.gpr .a3 = s.gpr .a3
  a7 : g.gpr .a7 = s.gpr .a7
  t5 : g.gpr .t5 = Tg s
  t6 : g.gpr .t6 = Dst s
  pres : ∀ r ∈ preserved, g.gpr r = s.gpr r
  sp : g.sp = Bs s + BitVec.ofNat 64 624
  rd : g.rd = s.rd
  wr : g.wr = FA s :: s.wr

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) :
    WP isa Impl.Gather.RISCV64.gather e (Gathered s) := by
  refine WP.mono (gather_wp e (gatherPre_of h he)) fun g ⟨mg, kg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  have hn : ∀ r, r ∉ gatherRegs → g.gpr r = e.gpr r := kg.gpr
  have hpres : ∀ r ∈ preserved, r ∉ gatherRegs := by decide
  exact ⟨mg, (hn _ (by decide)).trans he.a0, (hn _ (by decide)).trans he.a1, (hn _ (by decide)).trans he.a2,
    (hn _ (by decide)).trans he.a3, (hn _ (by decide)).trans he.a7, (hn _ (by decide)).trans he.t5,
    (hn _ (by decide)).trans he.t6, fun r hr => (hn r (hpres r hr)).trans (he.pres r hr),
    kg.sp.trans he.sp, kg.rd.trans he.rd, kg.wr.trans he.wr⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gMem s
  a0 : c.gpr .a0 = K s
  a1 : c.gpr .a1 = Nn s
  a2 : c.gpr .a2 = Ad s
  a3 : c.gpr .a3 = s.gpr .a3
  a4 : c.gpr .a4 = Dst s
  a5 : c.gpr .a5 = s.gpr .a7
  a6 : c.gpr .a6 = Tg s
  pres : ∀ r ∈ preserved, c.gpr r = s.gpr r
  sp : c.sp = Bs s + BitVec.ofNat 64 624
  rd : c.rd = s.rd
  wr : c.wr = FA s :: s.wr

theorem ready_wp {s g : State} (hg : Gathered s g) : WP isa (.block callArgs) g (Ready s) := by
  unfold callArgs
  simp only [mov]
  refine wp_mv fun u₁ v₁ => wp_mv fun u₂ v₂ => wp_mv fun u₃ v₃ => WP.block_nil ?_
  have g (r : Reg) (h4 : r ≠ .a4) (h5 : r ≠ .a5) (h6 : r ≠ .a6) : u₃.gpr r = g.gpr r := by
    rw [v₃.other r h6, v₂.other r h5, v₁.other r h4]
  have hpres : ∀ r ∈ preserved, r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .a6 := by decide
  exact ⟨by rw [v₃.mem, v₂.mem, v₁.mem, hg.mem], by rw [g _ (by decide) (by decide) (by decide), hg.a0],
    by rw [g _ (by decide) (by decide) (by decide), hg.a1], by rw [g _ (by decide) (by decide) (by decide), hg.a2],
    by rw [g _ (by decide) (by decide) (by decide), hg.a3],
    by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, hg.t6],
    by rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), hg.a7],
    by rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), hg.t5],
    fun r hr => by rw [g r (hpres r hr).1 (hpres r hr).2.1 (hpres r hr).2.2, hg.pres r hr],
    by rw [v₃.sp, v₂.sp, v₁.sp, hg.sp], by rw [v₃.rd, v₂.rd, v₁.rd, hg.rd], by rw [v₃.wr, v₂.wr, v₁.wr, hg.wr]⟩

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .a0 = K s ∧ c.callEntry.gpr .a1 = Nn s ∧ c.callEntry.gpr .a2 = Ad s ∧
      c.callEntry.gpr .a3 = s.gpr .a3 ∧ c.callEntry.gpr .a4 = Dst s ∧ c.callEntry.gpr .a5 = s.gpr .a7 ∧
      c.callEntry.gpr .a6 = Tg s :=
  ⟨by rw [c.callEntry_gpr (by decide), hc.a0], by rw [c.callEntry_gpr (by decide), hc.a1],
    by rw [c.callEntry_gpr (by decide), hc.a2], by rw [c.callEntry_gpr (by decide), hc.a3],
    by rw [c.callEntry_gpr (by decide), hc.a4], by rw [c.callEntry_gpr (by decide), hc.a5],
    by rw [c.callEntry_gpr (by decide), hc.a6]⟩

theorem cs_sub (s : State) : Bs s + BitVec.ofNat 64 624 - BitVec.ofNat 64 624 = Bs s := BitVec.add_sub_cancel _ _

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, od, ot, al, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨c3, c4, c5, c6, c7, c8, c9⟩ := hc.callGpr
  have hb := h.bs_toNat
  have hc24 : (Bs s + BitVec.ofNat 64 624).toNat = (Bs s).toNat + 624 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.hBn; omega_using [hb]
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c3, c4, c5, c6, c7, c8, c9, hc.sp, cs_sub]
    exact ⟨trivial, trivial, kd, kt, nd, nt, ad, at_, dt, h.bk.sub_left (stk_sub0 s _ (by decide)),
      h.bn.sub_left (stk_sub0 s _ (by decide)), h.ba.sub_left (stk_sub0 s _ (by decide)),
      h.bd.sub_left (stk_sub0 s _ (by decide)), h.bt.sub_left (stk_sub0 s _ (by decide)),
      ok, on, oa, od, ot, by rw [hc24]; omega_using [al, hb], by rw [hc24]; omega_using []⟩
  · refine covers_mem fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hc.rd, hc.wr, rd, wr]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · refine covers_mem fun r hr => ?_
    rw [hc.wr, wr]
    exact List.mem_cons_of_mem _ hr

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.read (raA s) 8 = s.gpr .ra
  out : encrypt (bytesAt (gMem s) (K s) 32) (bytesAt (gMem s) (Nn s) 12) (bytesAt (gMem s) (Ad s) (AL s))
      (bytesAt (gMem s) (Dst s) (L s)) = (bytesAt z.mem (Dst s) (L s), bytesAt z.mem (Tg s) 16)
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = Bs s + BitVec.ofNat 64 624
  rd : z.rd = s.rd
  wr : z.wr = FA s :: s.wr

theorem called_wp (hv : SealOk) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call "vg_chacha20_poly1305_seal_core" sealCode) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c3, c4, c5, c6, c7, c8, c9⟩ := hc.callGpr
  refine WP.callAny (k := Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624) hv (sealSpec_pre hcp) hcov hw
    (fun z rd' wr' sp' fr' pres' post' => ?_) (by rw [seal_sdepth]; decide)
  have hpost := sealSpec_post post'
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6, c7, c8, c9,
    hc.mem] at hpost
  -- The return address, from the frame, which the call kept.
  have ra : z.mem.read (raA s) 8 = s.gpr .ra := by
    rw [← h.gRa, ← hc.mem]
    refine Frame.read fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.bd.sub_left (stk_sub s 632 8 (by decide))
    · exact h.bt.sub_left (stk_sub s 632 8 (by decide))
    · simp only [below, hc.sp, seal_sdepth, cs_sub]
      exact Offset.disjoint_base _ (by decide) (by have := h.hBn; omega_arith)
  exact ⟨ra, hpost, fun r hr => by rw [pres' r hr, hc.pres r hr], sp'.trans hc.sp, rd'.trans hc.rd,
    wr'.trans hc.wr⟩

/-- The frame popped: the return address back, and what the function leaves. -/
theorem popped_ok {s z : State} (h : Lay s) (hz : Called s z) (m : Mem) (u : Nat → BitVec 64)
    (fl : Frame [⟨s.sp - 16, 16⟩] z.mem m) :
    abiPreserved s { popped .ra z with mem := m, unknowns := u } ∧
      gatherPost s { popped .ra z with mem := m, unknowns := u } := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, od, ot, al, w₁, w₂, hgl, hpm⟩ := h.pre
  have hra : z.mem.read (z.sp + 8) 8 = s.gpr .ra := by
    rw [hz.sp, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add]; exact hz.ra
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · show (z.write .ra _).gpr r = _
    rw [RegUpd.gpr_write_of_ne _ _ (show r ≠ .ra by revert r; decide), hz.pres r hr]
  · show z.sp + 16 = s.sp
    rw [hz.sp, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, Offset.add_add, h.hB]
  · show (z.write .ra (z.mem.read (z.sp + 8) 8)).gpr .ra = s.gpr .ra
    rw [RegUpd.gpr_write_self, hra]
  · show encrypt _ _ _ _ = (bytesAt m (Dst s) (L s), bytesAt m (Tg s) 16)
    -- The pop loses the frame's bytes, which lie apart from the data and the tag.
    have e : s.sp - 16 = Bs s + BitVec.ofNat 64 624 := by
      rw [h.hB, show (16 : Addr) = BitVec.ofNat 64 16 from rfl]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega_using []
    rw [e] at fl
    have hD : bytesAt m (Dst s) (L s) = bytesAt z.mem (Dst s) (L s) :=
      List.map_congr_left fun i hi =>
        lost_byte fl (R := dR s) (h.bd.symm.sub_right (stk_sub s 624 16 (by decide))) (List.mem_range.mp hi)
    have hT : bytesAt m (Tg s) 16 = bytesAt z.mem (Tg s) 16 :=
      List.map_congr_left fun i hi =>
        lost_byte fl (R := tgR s) (h.bt.symm.sub_right (stk_sub s 624 16 (by decide))) (List.mem_range.mp hi)
    rw [hD, hT]
    have hfc : Frame [FA s, dR s] s.mem (gMem s) :=
      (h.frame_eMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (⟨Bs s, 640⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FA s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right (stk_sub s 624 16 (by decide))
      · exact h₂
    have hk : bytesAt (gMem s) (K s) 32 = bytesAt s.mem (K s) 32 :=
      Proof.ChaCha20Poly1305.bytesAt_frame hfc (apart h.bk kd) (by omega_arith)
    have hn : bytesAt (gMem s) (Nn s) 12 = bytesAt s.mem (Nn s) 12 :=
      Proof.ChaCha20Poly1305.bytesAt_frame hfc (apart h.bn nd) (by omega_arith)
    have ha : bytesAt (gMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
      Proof.ChaCha20Poly1305.bytesAt_frame hfc (apart h.ba ad) (by omega_arith)
    have hd : bytesAt (gMem s) (Dst s) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact Proof.ChaCha20Poly1305.bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (s.gpr .a7).isLt)
    have := hz.out
    rw [hk, hn, ha, hd] at this
    exact this

theorem sealGather_wp (hv : SealOk) {s : State} (hs : gatherPre s) :
    WP isa sealGather s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.frame (by have := h.w₁; omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp hg) fun c hc => ?_)
  exact WP.mono (called_wp hv h hc) fun z hz m u fl => popped_ok h hz m u fl

end VG.Proof.ChaCha20Poly1305.RISCV64.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, RISC-V: constant time

Untrusted: everything here is checked by Lean. Two runs whose arguments and
descriptors agree (`gatherPub`) leak the same trace: the frame's push and
pop are at the stack pointer (`RelCT.frame`); the entry loads `tag` from the
stack; the gathering is constant time by `gather_rel`
(`Proof/Gather/RISCV64/LoopCT.lean`); and the call is constant time by its
callee's contract, whose public arguments agree (`sealGather_ct`). As on
PPC64LE (`Proof/ChaCha20Poly1305/PPC64LE/Gather/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Gather

open VG VG.RISCV64 VG.Impl.ChaCha20Poly1305.RISCV64.SealGather
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint ct_of gather_rel)

theorem sealGather_ct (hv : SealOk)
    (hct : ConstantTime isa (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pre
      (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pub sealCode) :
    ConstantTime isa gatherPre gatherPub sealGather := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, hdesc⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  refine (RelCT.frame (P := Eq2 σ₁ σ₂) (R := TT) (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp)
    ((?_ : RelCT isa (Eq2 (pushed .ra σ₁) (pushed .ra σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (show σ₁.sp - 16 = σ₂.sp - 16 by rw [qsp]) (by simp)
    (by taint_decide)) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← q7, ← q8, ← q9, ← q10] at g₂
  have hd : ∀ j < Cnt σ₁ * 16, e₁.mem (Src σ₁ + BitVec.ofNat 64 j) = e₂.mem (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega_using [hj, this])
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q7, ← q8]; exact hx
    rw [he₁.mem, he₂.mem, Lay.keepE h₁.bds.symm hx, Lay.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂ (by rw [he₁.sp, he₂.sp, hB])) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂)
    fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [] (by rw [hg₁.sp, hg₂.sp, hB]) (by simp) (by taint_decide))
    (ready_wp hg₁) (ready_wp hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by simp only [rdC, kR, nR, aR, K, Nn, Ad, AL, q3, q4, q5, q6]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, q9, q10, a0]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r3₁, r4₁, r5₁, r6₁, r7₁, r8₁, r9₁⟩ := hc₁.callGpr
  obtain ⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂⟩ := hc₂.callGpr
  exact RelCT.call hv hct (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
    subst ha hb
    refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ?_, cv₁, cw₁, cv₂, cw₂⟩
    simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, r3₁, r4₁, r5₁, r6₁, r7₁,
      r8₁, r9₁, r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, hc₁.sp, hc₂.sp, hB, K, Nn, Ad, Dst, Tg, q3, q4, q5, q6, q9,
      q10, a0, and_self]

end VG.Proof.ChaCha20Poly1305.RISCV64.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, RISCV64: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_chacha20_poly1305_seal_gather`, with the 640 bytes of stack below the
stack pointer that its frame and its call use
(`Spec.ChaCha20Poly1305.sealGatherContract`), implies the one the proof is
written against (`gatherRISCV64`, `gather_implies`), and so the code, calling
`vg_chacha20_poly1305_seal` by its shared contract (`seal_framed`), is
`Verified` against it (`sealGather_verified`). As on PPC64LE
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Gather

open VG VG.RISCV64 VG.Impl.ChaCha20Poly1305.RISCV64.SealGather

theorem sealGather_correct (s : State) (hs : gatherRISCV64.pre s) :
    ∃ t s', Exec isa sealGather s t s' ∧ abiPreserved s s' ∧ gatherRISCV64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := sealGather_wp seal_framed.1 hs
  exact ⟨t, s', he, ha, hp⟩

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl
theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)
theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)
theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
theorem pairFacts_ro (l : List (Region × Bool)) (h : ∀ a ∈ l, a.2 = false) : Sig.pairFacts l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [Sig.pairFacts, ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.append_nil]
    refine List.filterMap_eq_nil_iff.mpr fun b hb => ?_
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem gatherPre_of_spec {s : State} (h : (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640).pre s) :
    gatherPre s := by
  sig_pre [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.append_eq] at h
  rw [Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or,
    List.cons_append] at h
  obtain ⟨al, w₁, w₂, rd, wr, ⟨kd, kt, nd, nt, ad, at_, dt, dds, ⟨dl, da⟩, tds, tl, ta⟩,
    bk, bn, ba, bd, bt, ⟨bds, bl, barg⟩, ok, on, oa, od, ot, ⟨ods, ol⟩, hg, hpm⟩ := h
  exact ⟨rd, wr, kd, kt, nd, nt, ad, at_, dds.symm, tds.symm, fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩,
    dt, da, ta, bk, bn, ba, bds, bl, barg, bd, bt, ok, on, oa, ods, ol, od, ot, al, w₁, w₂, hg, hpm⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640).post s s' := by
  sig_post [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPost, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State}
    (hp : (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640).pub s₁ s₂) : gatherPub s₁ s₂ := by
  sig_pub [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.append_eq] at hp
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, q9, q10, a0, hd⟩ := hp
  exact ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, hd⟩

/-- A state satisfying the precondition of `vg_chacha20_poly1305_seal_gather`:
no slices, no additional data or text; the tag at `0x5000`, its address the
stack argument at `sp`. -/
def gatherSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9000, 8⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640).pre s := by
  sig_implies_sat [Spec.ChaCha20Poly1305.sealGatherContract, Spec.ChaCha20Poly1305.sealGatherSig,
    Spec.ChaCha20Poly1305.sealGatherPre, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.append_eq]
    [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.ChaCha20Poly1305.pMax] using gatherSat

theorem gather_implies : gatherRISCV64.Implies (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_verified :
    Verified RISCV64.target sealGather (Spec.ChaCha20Poly1305.sealGatherContract RISCV64.abi 640) :=
  Verified.of_correct (k := gatherRISCV64) sealGather_correct (sealGather_ct seal_framed.1 seal_framed.2.1)
    gather_implies

end VG.Proof.ChaCha20Poly1305.RISCV64.Gather
