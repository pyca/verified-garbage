module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# RSA with the CRT on x86-64: constant time of the loads into the primes'
workspaces

`loadArr j sp sl` clears an array of a prime's workspace (`zeroArr_ct`),
reads the bytes' pointer and length through the workspace's link, and loads
them (`loadArr_ct`): the link is pinned by correctness, the rest by the taint
analysis.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- A prime's workspace context with the same memory, `rdi` kept. -/
theorem SubCtx.mem {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx s B Z o w wx minv)
    (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : SubCtx t B Z o w wx minv :=
  ⟨h.scr.congr k.2.2, (k.gpr hr).trans h.rdi, hm ▸ h.hdr, hm ▸ h.link, hm ▸ h.nw, hm ▸ h.narr, h.lo, h.hi⟩

theorem LPre.mem {j sp sl : Nat} {p : BPub} {s t : State} (h : LPre j sp sl p s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : LPre j sp sl p t := by
  obtain ⟨minv, bs, hc, a1, a2, a3, a4, a5, a6, hp, hl, hbl, hsrc, b1, b2, b3⟩ := h
  exact ⟨minv, bs, hc.mem hm k hr, a1, a2, a3, a4, a5, a6, hm ▸ hp, hm ▸ hl, hbl,
    hsrc.congrK (by rw [hm]; exact InScr.refl _ _ _) k, b1, b2, b3⟩

/-- `zeroArr j` keeps `LPre`. -/
theorem LPre.zero {j sp sl : Nat} {p : BPub} {s : State} (h : LPre j sp sl p s) :
    WP isa (Crt.zeroArr j) s (LPre j sp sl p) := by
  obtain ⟨minv, bs, hc, hw2, hwx, hw30, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk', hkw⟩ := h
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  have h256 : 256 ≤ slot p.x.wx 8 := by unfold slot hdrBytes; omega
  have hJ := slot_le (w := p.x.wx) hj
  have hJ0 := hdr_lt_slot p.x.wx j (show 31 < 32 by decide)
  have ho64 : p.x.o < 2 ^ 64 := by omega
  have hr : ∀ r ∈ [(slot p.x.wx j, 8 * (p.x.wx + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.x.wx 8 := by
    simp only [List.mem_singleton, forall_eq]; omega
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) (by omega) hj) fun t ⟨_, ho₁, k₁⟩ => ?_
  have f₁ : Frm (off p.x.B p.x.o) [(slot p.x.wx j, 8 * (p.x.wx + 2))] s.mem t.mem := Frm.of_outside ho₁ (by simp)
  have hb : ∀ i < 32, word t.mem p.x.B (8 * i) = word s.mem p.x.B (8 * i) := fun i hi' =>
    f₁.word_below (fun r hr' => (hr r hr').2) (by omega) ho64 (by omega)
  refine ⟨minv, bs, hc.of_frm f₁ hr k₁.2.2 (k₁.gpr (by decide)), hw2, hwx, hw30, hj, hsp, hsl,
    (hb sp hsp).trans hp, (hb sl hsl).trans hl, hbl, hsrc.congrK ?_ k₁, hk1, hk', hkw⟩
  exact InScr.of_frm (f₁.rebase ho64 fun r hr' => by have := (hr r hr').2; omega) fun r hr' => by
    simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_singleton] at hr'
    subst hr'; simp only; omega

theorem pins_lpre {j sp sl : Nat} : Pins (LPre j sp sl) [.rdi] :=
  pins_of (fun p _ => off p.x.B p.x.o) fun _ _ ⟨_, _, hc, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.rdi

/-- The registers of `loadBE`. -/
def LRegs (j : Nat) (p : BPub) (t : State) : Prop :=
  t.gpr .rsi = p.ptr ∧ t.gpr .rcx = BitVec.ofNat 64 p.len ∧ t.gpr .rbx = off (off p.x.B p.x.o) (slot p.x.wx j)

/-- `loadArr j sp sl`, given that the taint analysis checks its header loads. -/
theorem loadArr_ct {j sp sl : Nat} (hj : j < 8) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hZ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r8 (.mem (hdr (sArr j))), .mov .r12 (.mem (hdr sW))])
      hc₁).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block [.mov .rsi (.mem (ws .rax sp)),
      .mov .rcx (.mem (ws .rax sl)), .mov .rbx (.mem (hdr (sArr j)))]) hc₂).isSome = true) :
    LoadCT j sp sl := by
  unfold LoadCT loadArr
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : BPub => (⟨off p.x.B p.x.o, slot p.x.wx 8, p.x.wx⟩ : Ws))
    (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (zeroArr_ct hj hZ)) fun p s h => h.zero) ?_
  refine RelCT.seq (RelCT.block_append (l₁ := ([.mov .rax (.mem (hdr sLink))] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => LPre j sp sl p t ∧ t.gpr .rax = p.x.B) [.rdi]
      (fun p s₁ s₂ h₁ h₂ => pins_lpre p s₁ s₂ h₁ h₂) (by taint_decide) ?_)
    (two_piece (Ψ := LRegs j) [.rdi, .rax]
      (pins_of (fun (p : BPub) r => if r = .rdi then off p.x.B p.x.o else p.x.B) fun p s ⟨⟨_, _, hc, _⟩, hax⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.rdi
        · exact hax) hT ?_)))
    (two_taint [.rsi, .rcx, .rbx] (pins_of (fun (p : BPub) r => if r = .rsi then p.ptr else if r = .rcx then
        BitVec.ofNat 64 p.len else off (off p.x.B p.x.o) (slot p.x.wx j)) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2) (by taint_decide))
  · intro p s h
    have h' := h
    obtain ⟨_, _, hc, -⟩ := h'
    have hn := hc.scr.nowrap
    have hi := hc.hi
    have hl₁ : InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * sLink)) 8 :=
      hc.good.scr.ld (by have := hdr_lt_slot p.x.wx 8 (show sLink < 32 by decide); omega)
    exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.x.B ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hc.rdi, hdrOff, hl₁, hc.link]) rfl)
      fun t ⟨⟨hax, hm⟩, k⟩ => ⟨h.mem hm k (by decide), hax⟩
  · rintro p s ⟨⟨_, bs, hc, -, -, -, hj, hsp, hsl, hp, hl, hbl, -⟩, hax⟩
    have hn := hc.scr.nowrap
    have hi := hc.hi
    have hlo := hc.lo
    have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
    have hl₁ : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off p.x.B p.x.o) (8 * i)) 8 := fun i hi' =>
      hc.good.scr.ld (by have := hdr_lt_slot p.x.wx 8 hi'; omega)
    have hln : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.x.B (8 * i)) 8 := fun i hi' =>
      hc.scr.ld (by omega)
    unfold LRegs; rw [← hbl]
    exact WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = p.ptr ∧
        t.gpr .rcx = BitVec.ofNat 64 bs.length ∧ t.gpr .rbx = off (off p.x.B p.x.o) (slot p.x.wx j))
      (by xrun [State.ea, hdr, ws, hc.rdi, hax, hdrOff, hln sp hsp, hp, hln sl hsl, hl,
        hl₁ (sArr j) (by unfold sArr; omega), hc.hdr.harr j hj]) rfl) fun t h => h.1

theorem loadArr_ct_pN : LoadCT Public.aN sP sPlen := loadArr_ct (by decide) (by taint_decide) (by taint_decide)

theorem loadArr_ct_pI : LoadCT aChunk sQinv sPlen := loadArr_ct (by decide) (by taint_decide) (by taint_decide)

theorem loadArr_ct_qN : LoadCT Public.aN sQ sQlen := loadArr_ct (by decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
