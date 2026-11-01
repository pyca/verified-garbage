module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintUnpackMain
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintUnpackMain
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintCT
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RelCT

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_unpack`, constant time and `Verified`

Constant time but for its input, as on AArch64: zeroing `h` leaks only the
pointers and `hlen` (the taint analysis), and leaves states that agree on
`k`, `ω`, the pointers and the index, and on all the memory the rest may
access (the input `y`, which the contract lets it leak, and `h`, zeroed);
`memTaint` proves the rest. `omega` is a `u32`, whose register's upper bits
the two runs need not agree on: the code zero-extends it before using it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.RISCV64.Pack.Hint (MAgree memTaint wp_sp)

theorem pre_of {s : State} (h : (hintBitUnpackContract RISCV64.abi).pre s) : UPre s := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The public registers after zeroing `h`: `y`, `ω`, `h`, the index and `k`. -/
abbrev hbuTaint : VG.RISCV64.Taint.T := VG.RISCV64.Taint.ofRegs [.a0, .a2, .a3, .t1, .t2]

theorem ct : ConstantTime isa (hintBitUnpackContract RISCV64.abi).pre (hintBitUnpackContract RISCV64.abi).pub
    Impl.MlDsa.RISCV64.Pack.hintBitUnpack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.RISCV64.Pack.hintBitUnpack
  refine RelCT.seq (R := MAgree hbuTaint) ?_
    (RelCT.taint (A := memTaint) hbuTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := fun (s₀ s : State) => ZPost s₀ s ∧ s.sp = s₀.sp)
    (RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.a3, .a4]) ?_ (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨wp_sp (zero_ok (pre_of hx)), wp_sp (zero_ok (pre_of hy))⟩)) (fun _ _ h => h) ?_
  · rintro a b ⟨_, _, hab⟩
    sig_pub [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs] at hab
    obtain ⟨hsp, -, -, -, -, h6, h7⟩ := hab
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h6
    · exact h7
  rintro x' y' ⟨_, x, y, ⟨hx, hy, hpb⟩, ⟨fx, spx⟩, ⟨fy, spy⟩⟩
  have px := pre_of hx
  have py := pre_of hy
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs] at hpb
  obtain ⟨hsp, hleak, p3, p4, p5, p6, p7⟩ := hpb
  have hω : uω x = uω y := by simp only [uω, w32, p5]
  have hrd : x'.rd = y'.rd := by rw [fx.com.rd, fy.com.rd, px.rd, py.rd]; simp only [uyR, uY, uLen, p3, p4]
  have hwr : x'.wr = y'.wr := by rw [fx.com.wr, fy.com.wr, px.wr, py.wr]; simp only [uhR, uH, p6, p7]
  refine ⟨⟨by rw [spx, spy, hsp], fun r hr => ?_⟩, hrd, hwr, fun a ha => ?_⟩
  · simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [fx.com.a0, fy.com.a0]; simp only [uY, p3]
    · rw [fx.com.a2, fy.com.a2, hω]
    · rw [fx.a3, fy.a3]; simp only [uH, p6]
    · rw [fx.t1, fy.t1]
    · rw [fx.t2, fy.t2]; simp only [uk, uLen, p4, hω]
  · rw [fx.com.rd, fx.com.wr, px.rd, px.wr] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- `y`: as on entry, where the runs agree.
      have hxy : ¬ (uhR x).Contains a 1 := fun hc' => px.d_yh a hc hc'
      rw [fx.com.frame a (fun r hr hc' => by simp only [List.mem_singleton] at hr; subst hr; exact hxy hc'),
        fy.com.frame a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [uhR, uH, ← p6, ← p7] at hc'
          exact hxy hc')]
      have hb : bytesAt x.mem (uY x) (uLen x) = bytesAt y.mem (uY y) (uLen y) := map_toNat_inj hleak
      have hlt : (a - uY x).toNat < uLen x := by simp only [Region.Contains] at hc; omega
      have fY := px.fitY
      have ea : a = uY x + BitVec.ofNat 64 (a - uY x).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have := congrArg (fun l => l.getD (a - uY x).toNat 0) hb
      rw [VG.Proof.MlKem.bytesAt_getD _ _ hlt, VG.Proof.MlKem.bytesAt_getD _ _ (show _ < uLen y by
        simpa only [uLen, ← p4] using hlt), ← ea, show uY y = uY x by simp only [uY, p3], ← ea] at this
      exact this
    · -- `h`: zeros.
      have hl := px.hlen
      have h₁ := byte_of_zero_words (m := x'.mem) (p := uH x) (N := (x.gpr .a4).toNat)
        (fun t ht => fx.zero t (by omega)) hc
      have h₂ := byte_of_zero_words (m := y'.mem) (p := uH y) (N := (y.gpr .a4).toNat)
        (fun t ht => fy.zero t (by have := py.hlen; omega)) (by simpa only [uhR, uH, ← p6, ← p7] using hc)
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 84 | .a2 => 80 | .a3 => 0x3000 | .a4 => 1024 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 84⟩]
  wr := [⟨0x3000, 4096⟩]

end VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Spec.MlDsa
open VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

theorem hintBitUnpack_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Pack.hintBitUnpack (hintBitUnpackContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, ct, ⟨satState, ?_⟩⟩
  · obtain ⟨t, s', he, hpost, hk⟩ := correct (pre_of hs)
    refine ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), ?_⟩
    sig_post [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs]
    exact hpost
  · sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Region.disjoint_of_sep (by decide)
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Pack
