module

public import VerifiedGarbage.Proof.Gather.RISCV64.Loop
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Gather.Contract
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Impl.AesGcm.RISCV64.SealGather
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-!
# AES-GCM encryption out of place, from a list of slices, RISC-V: the function

Untrusted: everything here is checked by Lean. With `Bs` the base of the
4640 bytes of stack below the stack pointer (`sp = Bs + 4640`),
`vg_aes_gcm_seal_gather` pushes its frame of 16 bytes at `Bs + 4624`, which
keeps our return address at `Bs + 4632`; puts `tag`, from our stack
arguments above the frame, at `Bs + 4624`, the call's stack argument; keeps
`aad` and `aad_len` in `t5` and `t6` and `len` in `a7` (`entered_wp`);
gathers the slices to `dst` (`gathered_wp`); and calls `vg_aes_gcm_seal`
on them in place, by its contract (`sealSpec_pre`, `sealSpec_post`), whose
frame is in the 4624 bytes below ours, so the return address comes back
from it (`sealGather_wp`). As for ChaCha20-Poly1305
(`Proof/ChaCha20Poly1305/RISCV64/Gather/Fn.lean`), with the call's stack
argument as on PPC64LE (`Proof/AesGcm/PPC64LE/Gather/Fn.lean`).
-/

@[expose] public section

/-! ## The function called

`vg_aes_gcm_seal_gather`
calls `vg_aes_gcm_seal`, with its working space in a frame of its own, by
its shared contract (`Spec.Gcm.sealContract`, with 4624 bytes of stack,
which its frame uses: `seal_sdepth`): its precondition from the layout the
call gives it (`callPre`: its stack argument `tag` in our frame,
`sealSpec_pre`), its postcondition (`sealSpec_post`) and its public data
(`sealSpec_pub`). As for ChaCha20-Poly1305
(`Proof/ChaCha20Poly1305/RISCV64/Gather/Callee.lean`), and as on PPC64LE
(`Proof/AesGcm/PPC64LE/Gather/Callee.lean`).
-/

namespace VG.Proof.AesGcm.RISCV64.Gather

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)

/-- The frame of `vg_aes_gcm_seal` uses the 4624 bytes of stack its
contract reserves. -/
theorem seal_sdepth : sdepth Impl.AesGcm.RISCV64.SealGather.sealCode = 4624 := by
  decide +kernel

/-- What a call of `vg_aes_gcm_seal(ctx = a0, rounds = a1, nonce = a2,
nonce_len = a3, aad = a4, aad_len = a5, data = a6, len = a7, tag)` needs,
`tag` its stack argument. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let arg : Region := ⟨stackArgAddr s 0, 8⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 4624, 4624⟩
  s.rd = [ctx, nonce, aad, arg] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧ data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 4624 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) ∧ (s.gpr .a0).toNat % 8 = 0

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.Gcm.sealContract RISCV64.abi 4624).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇⟩ := h
  sig_pre [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.range, List.range.loop]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, RISCV64.abi, RISCV64.argRegs, List.getD,
    stackArgs_one, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.Gcm.sealContract RISCV64.abi 4624).post s s')
    (hR : (s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) :
    encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxH s.mem (s.gpr .a0)) 16
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
        (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat, bytesAt s'.mem (stackArg s 0) 16) := by
  sig_post [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPost, RISCV64.abi, RISCV64.argRegs,
    stackArgs_one, List.range, List.range.loop] at h
  exact h hR

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0) :
    (Spec.Gcm.sealContract RISCV64.abi 4624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.sealContract, Spec.Gcm.sealSig, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.range, List.range.loop]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.range, List.range.loop]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.AesGcm.RISCV64.Gather

namespace VG.Proof.AesGcm.RISCV64.Gather

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesGcm.RISCV64.SealGather VG.WriteBytes
open VG.Impl.AesGcm.RISCV64 (mov)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)
open VG.Proof.Gather.RISCV64 (GatherPre gather_wp gatherRegs)

/-- The correctness of `vg_aes_gcm_seal`, in its frame, by its shared contract. -/
abbrev SealOk : Prop :=
  ∀ s, (Spec.Gcm.sealContract RISCV64.abi 4624).pre s →
    ∃ t s', Exec isa sealCode s t s' ∧ abiPreserved s s' ∧ (Spec.Gcm.sealContract RISCV64.abi 4624).post s s'

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  Covers.of_sub fun r hr => ⟨r, h r hr, 0, (BitVec.add_zero _).symm, by omega_arith⟩

theorem contains_pre {a : Addr} {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 4640 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 4640

/-- Our frame; the call's stack argument and the return address in it. -/
abbrev FA : Region := ⟨Bs s + BitVec.ofNat 64 4624, 16⟩
abbrev aOut : Addr := Bs s + BitVec.ofNat 64 4624
abbrev raA : Addr := Bs s + BitVec.ofNat 64 4632

/-- Our stack argument `i`. -/
abbrev sa (i : Nat) : Addr := Bs s + BitVec.ofNat 64 (4640 + 8 * i)

/-- The memory after the push, and after the entry. -/
abbrev eMem0 : Mem := s.mem.write (raA s) 8 (s.gpr .ra)
abbrev eMem : Mem := (eMem0 s).writeW (aOut s) (Tg s)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gMem : Mem := writeBytes (eMem s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_aes_gcm_seal` reads and writes. -/
abbrev rdC : List Region := [cR s, nR s, aR s, ⟨aOut s, 8⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 4640
  hBn : (Bs s).toNat + 4664 ≤ 2 ^ 64
  bc : (⟨Bs s, 4640⟩ : Region).Disjoint (cR s)
  bn : (⟨Bs s, 4640⟩ : Region).Disjoint (nR s)
  ba : (⟨Bs s, 4640⟩ : Region).Disjoint (aR s)
  bds : (⟨Bs s, 4640⟩ : Region).Disjoint (dsR s)
  bl : ∀ r ∈ lsR s, (⟨Bs s, 4640⟩ : Region).Disjoint r
  bd : (⟨Bs s, 4640⟩ : Region).Disjoint (dR s)
  bt : (⟨Bs s, 4640⟩ : Region).Disjoint (tgR s)
  hargR : argR s = ⟨Bs s + BitVec.ofNat 64 4640, 24⟩
  al : s.sp.toNat % 16 = 0
  w₁ : 4640 ≤ s.sp.toNat
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64
  hR : Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bc, bn, ba, bds, bl, barg, bd, bt,
    oc, on, oa, ods, ol, od, ot, al, w₁, w₂, hR, hgl, ca⟩ := hs
  have hB : s.sp = Bs s + BitVec.ofNat 64 4640 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 4664 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega_arith
  refine ⟨⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bc, bn, ba, bds, bl, barg, bd, bt,
    oc, on, oa, ods, ol, od, ot, al, w₁, w₂, hR, hgl, ca⟩, hB, hBn, bc, bn, ba, bds, bl, bd, bt, ?_, al, w₁, hgl,
    ods, hR⟩
  show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 24⟩ : Region) = ⟨Bs s + BitVec.ofNat 64 4640, 24⟩
  rw [← hB]; simp

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 4640) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 4640⟩ :=
  Offset.sub_base _ h'

theorem stk_sub0 (s : State) (n : Nat) (h' : n ≤ 4640) : (⟨Bs s, n⟩ : Region).Sub ⟨Bs s, 4640⟩ :=
  Region.sub_prefix h'

theorem frame_eMem0 (s : State) : Frame [FA s] s.mem (eMem0 s) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _
    (Offset.contains (Bs s) (d := 4632) (e := 4624) (by decide) (by decide) (by
      have := (Bs s).isLt; omega_arith))

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem bs_toNat : (Bs s).toNat = s.sp.toNat - 4640 := by
  have e := congrArg BitVec.toNat h.hB
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
  have := h.hBn
  omega

theorem off_toNat {k : Nat} (hk : k < 4664) : (Bs s + BitVec.ofNat 64 k).toNat = (Bs s).toNat + k := by
  have := h.hBn
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem al8 {k : Nat} (hk : k < 4664) (h8 : k % 8 = 0) : (Bs s + BitVec.ofNat 64 k).toNat % 8 = 0 := by
  rw [h.off_toNat hk, h.bs_toNat]; have := h.al; have := h.w₁; omega

theorem fsp : s.sp - 16 = Bs s + BitVec.ofNat 64 4624 := by
  rw [h.hB, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, Offset.add_ofNat_sub _ (by decide)]

theorem fra : s.sp - 16 + 8 = raA s := by
  rw [h.fsp, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add]

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

/-- Our stack argument `i`, from its address in our frame's terms. -/
theorem sa_eq {i : Nat} : stackArg s i = s.mem.readW (sa s i) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (8 * i)) 64 = _
  rw [h.hB, Offset.add_add]

theorem sa_in {i : Nat} (hi : i < 3) (u : State) (hrd : u.rd = s.rd) :
    InRegions (u.rd ++ u.wr) (sa s i) 8 :=
  ⟨_, List.mem_append_left _ (by rw [hrd]; exact h.argIn), by
    rw [h.hargR]
    exact Offset.contains (Bs s) (by omega_arith) (by omega_arith) (by have := h.hBn; omega_arith)⟩

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 4640⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x := by
  have hf : Frame [FA s] s.mem (eMem s) :=
    (frame_eMem0 s).writeW (List.mem_singleton_self _) _
      (contains_pre (by decide))
  exact hf x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 4624 16 (by decide) x hc)

omit h in
theorem frame_eMem : Frame [FA s] s.mem (eMem s) :=
  (frame_eMem0 s).writeW (List.mem_singleton_self _) _ (contains_pre (by decide))

/-- Our stack arguments are apart from the frame. -/
theorem sa_fa {i : Nat} (hi : i < 3) : ∀ r ∈ [FA s], (⟨sa s i, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (.inr (by omega_arith)) (by have := h.hBn; omega_arith)
    (by have := h.hBn; omega_arith)

/-- Our stack arguments, after the push and after the entry. -/
theorem e0Arg {i : Nat} (hi : i < 3) : (eMem0 s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (frame_eMem0 s) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

theorem eArg {i : Nat} (hi : i < 3) : (eMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (Lay.frame_eMem (s := s)) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eMem s x := by
  intro r hr x hx
  refine (keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bl r hr).symm

theorem hpt : gathered 64 (eMem s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gMem : Frame [dR s] (eMem s) (gMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A doubleword of the frame, once the slices are gathered. -/
theorem gFr {a : Nat} (ha : a + 8 ≤ 16) :
    (gMem s).read (Bs s + BitVec.ofNat 64 (4624 + a)) 8 = (eMem s).read (Bs s + BitVec.ofNat 64 (4624 + a)) 8 :=
  Frame.read h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.bd.sub_left (stk_sub s _ _ (by omega_arith))) (by decide)

/-- The return address and the call's `tag`, once the slices are gathered. -/
theorem gRa : (gMem s).read (raA s) 8 = s.gpr .ra := by
  rw [show raA s = Bs s + BitVec.ofNat 64 (4624 + 8) from rfl, h.gFr (by decide), eMem, Mem.writeW,
    Mem.read_write_sep (Offset.sep _ (.inr (by decide)) (by have := h.hBn; omega_arith)
      (by have := h.hBn; omega_arith)) (by decide)]
  exact read_write_self _ _ _

theorem gTag : (gMem s).readW (aOut s) 64 = Tg s := by
  rw [Mem.readW, show aOut s = Bs s + BitVec.ofNat 64 (4624 + 0) from rfl, h.gFr (by decide), ← Mem.readW]
  exact Mem.readW_writeW_self64 _ _ _

/-- Our stack arguments, once the slices are gathered. -/
theorem gArg {i : Nat} (hi : i < 3) : (gMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have darg := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [h.hargR] at darg
    refine darg.symm.sub_left ?_
    exact Offset.sub _ (by omega_arith) (by omega_arith)) (by decide), h.eArg hi]

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
  a5 : e.gpr .a5 = s.gpr .a7
  a6 : e.gpr .a6 = Dst s
  a7 : e.gpr .a7 = stackArg s 1
  t5 : e.gpr .t5 = Ad s
  t6 : e.gpr .t6 = s.gpr .a5
  pres : ∀ r ∈ preserved, e.gpr r = s.gpr r
  sp : e.sp = Bs s + BitVec.ofNat 64 4624
  rd : e.rd = s.rd
  wr : e.wr = FA s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (pushed .ra s) (Entered s) := by
  have asp : (pushed .ra s).sp = Bs s + BitVec.ofNat 64 4624 := h.fsp
  have amem : (pushed .ra s).mem = eMem0 s := by
    show s.mem.write (s.sp - 16 + 8) 8 (s.gpr .ra) = _
    rw [h.fra]
  have awr : (pushed .ra s).wr = FA s :: s.wr := by
    show ⟨s.sp - 16, 16⟩ :: s.wr = _; rw [h.fsp]
  have ag (r : Reg) : (pushed .ra s).gpr r = s.gpr r := rfl
  have ard : (pushed .ra s).rd = s.rd := rfl
  unfold entry
  simp only [mov]
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .t0 = Bs s + BitVec.ofNat 64 4624 := by rw [v₁.gpr, asp, BitVec.add_zero]
  refine wp_ld (a := sa s 2) (by decide) (by rw [p₁, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ (by rw [v₁.rd, ard])) fun u₂ v₂ => ?_
  have p₂ : u₂.gpr .t0 = Bs s + BitVec.ofNat 64 4624 := by rw [v₂.other _ (by decide), p₁]
  have t₂ : u₂.gpr .t1 = Tg s := by rw [v₂.gpr, v₁.mem, amem, h.e0Arg (by decide)]
  refine wp_sd (a := aOut s) (by decide) (by rw [p₂, BitVec.add_zero]) (h.al8 (by decide) (by decide))
    ⟨_, by rw [v₂.wr, v₁.wr, awr]; exact List.mem_cons_self .., contains_pre (by decide)⟩
    fun u₃ v₃ => ?_
  have m₃ : u₃.mem = eMem s := by rw [v₃.mem, t₂, v₂.mem, v₁.mem, amem]
  refine wp_mv fun u₄ v₄ => wp_mv fun u₅ v₅ => wp_mv fun u₆ v₆ => wp_mv fun u₇ v₇ => ?_
  have p₇ : u₇.gpr .t0 = Bs s + BitVec.ofNat 64 4624 := by
    rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.gpr, p₂]
  have hm₇ : u₇.mem = eMem s := by rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, m₃]
  have hr₇ : u₇.rd = s.rd := by rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, ard]
  refine wp_ld (a := sa s 0) (by decide) (by rw [p₇, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ hr₇) fun u₈ v₈ => ?_
  refine wp_ld (a := sa s 1) (by decide) (by rw [v₈.other _ (by decide), p₇, Offset.add_add])
    (h.al8 (by decide) (by decide)) (h.sa_in (by decide) _ (by rw [v₈.rd, hr₇])) fun u₉ v₉ => WP.block_nil ?_
  have g (r : Reg) (h0 : r ≠ .t0) (h1 : r ≠ .t1) (h5 : r ≠ .t5) (h6 : r ≠ .t6) (h4 : r ≠ .a4) (h5' : r ≠ .a5)
      (h6' : r ≠ .a6) (h7 : r ≠ .a7) : u₉.gpr r = s.gpr r := by
    rw [v₉.other r h7, v₈.other r h6', v₇.other r h5', v₆.other r h4, v₅.other r h6, v₄.other r h5, v₃.gpr,
      v₂.other r h1, v₁.other r h0, ag]
  have hpres : ∀ r ∈ preserved, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t5 ∧ r ≠ .t6 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .a6 ∧
      r ≠ .a7 := by decide
  have pre (r : Reg) : u₃.gpr r = s.gpr r ∨ r = .t0 ∨ r = .t1 := by
    by_cases a : r = .t0
    · exact .inr (.inl a)
    by_cases b : r = .t1
    · exact .inr (.inr b)
    exact .inl (by rw [v₃.gpr, v₂.other r b, v₁.other r a, ag])
  exact ⟨by rw [v₉.mem, v₈.mem, hm₇], g _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr,
      v₅.other _ (by decide), v₄.other _ (by decide), (pre .a6).resolve_right (by decide)],
    by rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.other _ (by decide),
      v₅.other _ (by decide), v₄.other _ (by decide), (pre .a7).resolve_right (by decide)],
    by rw [v₉.other _ (by decide), v₈.gpr, v₇.mem, v₆.mem, v₅.mem, v₄.mem, m₃, h.eArg (by decide)],
    by rw [v₉.gpr, v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, m₃, h.eArg (by decide)],
    by rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide),
      v₅.other _ (by decide), v₄.gpr, (pre .a4).resolve_right (by decide)],
    by rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide),
      v₅.gpr, v₄.other _ (by decide), (pre .a5).resolve_right (by decide)],
    fun r hr => have q := hpres r hr; g r q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
      q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2,
    by rw [v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, asp],
    by rw [v₉.rd, v₈.rd, hr₇],
    by rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, awr]⟩

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bc, bn, ba, bds, bl, barg, bd, bt,
    oc, on, oa, ods, ol, od, ot, al, w₁, w₂, hR, hgl, ca⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { a4 := he.a4
          a5 := by rw [he.a5, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          a6 := he.a6
          hcnt := (s.gpr .a7).isLt
          dw := ods
          lt := (stackArg s 1).isLt
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
  a7 : g.gpr .a7 = stackArg s 1
  t5 : g.gpr .t5 = Ad s
  t6 : g.gpr .t6 = s.gpr .a5
  pres : ∀ r ∈ preserved, g.gpr r = s.gpr r
  sp : g.sp = Bs s + BitVec.ofNat 64 4624
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
  a0 : c.gpr .a0 = C s
  a1 : c.gpr .a1 = s.gpr .a1
  a2 : c.gpr .a2 = Nn s
  a3 : c.gpr .a3 = s.gpr .a3
  a4 : c.gpr .a4 = Ad s
  a5 : c.gpr .a5 = s.gpr .a5
  a6 : c.gpr .a6 = Dst s
  a7 : c.gpr .a7 = stackArg s 1
  pres : ∀ r ∈ preserved, c.gpr r = s.gpr r
  sp : c.sp = Bs s + BitVec.ofNat 64 4624
  rd : c.rd = s.rd
  wr : c.wr = FA s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgs) g (Ready s) := by
  unfold callArgs
  simp only [mov]
  refine wp_mv fun u₁ v₁ => wp_mv fun u₂ v₂ => wp_addSp (imm := 0) (by decide) fun u₃ v₃ => ?_
  have p₃ : u₃.gpr .t0 = Bs s + BitVec.ofNat 64 4624 := by rw [v₃.gpr, v₂.sp, v₁.sp, hg.sp, BitVec.add_zero]
  refine wp_ld (a := sa s 0) (by decide) (by rw [p₃, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ (by rw [v₃.rd, v₂.rd, v₁.rd, hg.rd])) fun u₄ v₄ => WP.block_nil ?_
  have g (r : Reg) (h4 : r ≠ .a4) (h5 : r ≠ .a5) (h0 : r ≠ .t0) (h6 : r ≠ .a6) : u₄.gpr r = g.gpr r := by
    rw [v₄.other r h6, v₃.other r h0, v₂.other r h5, v₁.other r h4]
  have hpres : ∀ r ∈ preserved, r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .t0 ∧ r ≠ .a6 := by decide
  exact ⟨by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, hg.mem],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a1],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a2],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a3],
    by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, hg.t5],
    by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), hg.t6],
    by rw [v₄.gpr, v₃.mem, v₂.mem, v₁.mem, hg.mem, h.gArg (by decide)],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a7],
    fun r hr => have q := hpres r hr; by rw [g r q.1 q.2.1 q.2.2.1 q.2.2.2, hg.pres r hr],
    by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, hg.sp], by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, hg.rd],
    by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, hg.wr]⟩

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .a0 = C s ∧ c.callEntry.gpr .a1 = s.gpr .a1 ∧ c.callEntry.gpr .a2 = Nn s ∧
      c.callEntry.gpr .a3 = s.gpr .a3 ∧ c.callEntry.gpr .a4 = Ad s ∧ c.callEntry.gpr .a5 = s.gpr .a5 ∧
      c.callEntry.gpr .a6 = Dst s ∧ c.callEntry.gpr .a7 = stackArg s 1 :=
  ⟨by rw [c.callEntry_gpr (by decide), hc.a0], by rw [c.callEntry_gpr (by decide), hc.a1],
    by rw [c.callEntry_gpr (by decide), hc.a2], by rw [c.callEntry_gpr (by decide), hc.a3],
    by rw [c.callEntry_gpr (by decide), hc.a4], by rw [c.callEntry_gpr (by decide), hc.a5],
    by rw [c.callEntry_gpr (by decide), hc.a6], by rw [c.callEntry_gpr (by decide), hc.a7]⟩

theorem cs_sub (s : State) : Bs s + BitVec.ofNat 64 4624 - BitVec.ofNat 64 4624 = Bs s :=
  BitVec.add_sub_cancel _ _

theorem Ready.argAddr {s c : State} (hc : Ready s c) (rd wr : List Region) :
    stackArgAddr ((c.callEntry).withRegions rd wr) 0 = aOut s := by
  show c.sp + BitVec.ofNat 64 (8 * 0) = _
  rw [hc.sp, Nat.mul_zero, BitVec.add_zero]

theorem Ready.arg {s c : State} (h : Lay s) (hc : Ready s c) (rd wr : List Region) :
    stackArg ((c.callEntry).withRegions rd wr) 0 = Tg s := by
  show c.mem.readW (stackArgAddr ((c.callEntry).withRegions rd wr) 0) 64 = _
  rw [hc.argAddr, hc.mem, h.gTag]

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    oc, on, oa, ods, ol, od, ot, al, w₁, w₂, hR, hgl, ca⟩ := h.pre
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr
  have hBn := h.hBn
  have hb := h.bs_toNat
  have h24 := h.off_toNat (k := 4624) (by decide)
  have aS : (⟨aOut s, 8⟩ : Region).Sub ⟨Bs s, 4640⟩ := stk_sub s 4624 8 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c3, c4, c5, c6, c7, c8, c9, c10, hc.sp, cs_sub, hc.argAddr, hc.arg h]
    refine ⟨trivial, trivial, cd, ct, nd, nt, ad, at_, dt, h.bd.symm.sub_right aS, h.bt.symm.sub_right aS,
      h.bc.sub_left (stk_sub0 s _ (by decide)), h.bn.sub_left (stk_sub0 s _ (by decide)),
      h.ba.sub_left (stk_sub0 s _ (by decide)), h.bd.sub_left (stk_sub0 s _ (by decide)),
      h.bt.sub_left (stk_sub0 s _ (by decide)), (Offset.disjoint_base _ (by decide) (by omega_arith)).symm,
      oc, on, oa, od, ot, by rw [h24]; omega_arith, by rw [h24]; omega_arith, by rw [h24]; omega_arith,
      hR, ca⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨FA s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 0,
        (BitVec.add_zero _).symm, by show 0 + 8 ≤ 16; omega_arith⟩
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
  · refine covers_mem fun r hr => ?_
    rw [hc.wr, wr]
    exact List.mem_cons_of_mem _ hr

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.read (raA s) 8 = s.gpr .ra
  out : encryptWith (ctxCiph (gMem s) (C s) (Rn s)) (ctxH (gMem s) (C s)) 16 (bytesAt (gMem s) (Nn s) (NL s))
      (bytesAt (gMem s) (Dst s) (L s)) (bytesAt (gMem s) (Ad s) (AL s)) =
    (bytesAt z.mem (Dst s) (L s), bytesAt z.mem (Tg s) 16)
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = Bs s + BitVec.ofNat 64 4624
  rd : z.rd = s.rd
  wr : z.wr = FA s :: s.wr

theorem called_wp (hv : SealOk) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call "vg_aes_gcm_seal" sealCode) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr
  refine WP.callAny (k := Spec.Gcm.sealContract RISCV64.abi 4624) hv (sealSpec_pre hcp) hcov hw
    (fun z rd' wr' sp' fr' pres' post' => ?_) (by rw [seal_sdepth]; decide)
  have hpost := sealSpec_post post' (by simp only [State.withRegions_gpr, c4]; exact h.hR)
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6, c7, c8, c9, c10,
    hc.mem, hc.arg h] at hpost
  -- The return address, from the frame, which the call kept.
  have ra : z.mem.read (raA s) 8 = s.gpr .ra := by
    rw [← h.gRa, ← hc.mem]
    refine Frame.read fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.bd.sub_left (stk_sub s 4632 8 (by decide))
    · exact h.bt.sub_left (stk_sub s 4632 8 (by decide))
    · simp only [below, hc.sp, seal_sdepth, cs_sub]
      exact Offset.disjoint_base _ (by decide) (by have := h.hBn; omega_arith)
  exact ⟨ra, hpost, fun r hr => by rw [pres' r hr, hc.pres r hr], sp'.trans hc.sp, rd'.trans hc.rd,
    wr'.trans hc.wr⟩

/-- The frame popped: the return address back, and what the function leaves. -/
theorem popped_ok {s z : State} (h : Lay s) (hz : Called s z) :
    abiPreserved s (popped .ra z) ∧ gatherPost s (popped .ra z) := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    oc, on, oa, ods, ol, od, ot, al, w₁, w₂, hR, hgl, ca⟩ := h.pre
  have hra : z.mem.read (z.sp + 8) 8 = s.gpr .ra := by
    rw [hz.sp, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add]; exact hz.ra
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · show (z.write .ra _).gpr r = _
    rw [RegUpd.gpr_write_of_ne _ _ (show r ≠ .ra by revert r; decide), hz.pres r hr]
  · show z.sp + 16 = s.sp
    rw [hz.sp, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, Offset.add_add, h.hB]
  · show (z.write .ra (z.mem.read (z.sp + 8) 8)).gpr .ra = s.gpr .ra
    rw [RegUpd.gpr_write_self, hra]
  · show encryptWith _ _ _ _ _ _ = (bytesAt (z.write .ra (z.mem.read (z.sp + 8) 8)).mem (Dst s) (L s),
      bytesAt (z.write .ra (z.mem.read (z.sp + 8) 8)).mem (Tg s) 16)
    rw [RegUpd.mem_write]
    have hfc : Frame [FA s, dR s] s.mem (gMem s) :=
      ((Lay.frame_eMem (s := s)).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (⟨Bs s, 4640⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FA s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right (stk_sub s 4624 16 (by decide))
      · exact h₂
    obtain ⟨hc₁, hh₁⟩ := Proof.AesGcm.ctx_frame hfc (apart h.bc cd) h.hR
    have hn : bytesAt (gMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
      Proof.Cmac.bytesAt_frame hfc (apart h.bn nd) (by omega_arith)
    have ha : bytesAt (gMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
      Proof.Cmac.bytesAt_frame hfc (apart h.ba ad) (by omega_arith)
    have hd : bytesAt (gMem s) (Dst s) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact Proof.AesGcm.bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (stackArg s 1).isLt)
    have := hz.out
    rw [hc₁, hh₁, hn, ha, hd] at this
    exact this

theorem sealGather_wp (hv : SealOk) {s : State} (hs : gatherPre s) :
    WP isa sealGather s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.frame (by have := h.w₁; omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  exact WP.mono (called_wp hv h hc) fun z hz => popped_ok h hz

end VG.Proof.AesGcm.RISCV64.Gather
