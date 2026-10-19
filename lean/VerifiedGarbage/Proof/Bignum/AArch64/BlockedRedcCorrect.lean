module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBody

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

theorem redc_code_eq : VG.Impl.Bignum.AArch64.BlockedRedc.redc =
    .seq (.block [.lsr .x .x12 .x12 3, movi .x10 0])
      (.seq (.loop rowBody (.nonzero .x .x12))
        (.block [ldh .x12 sW, .lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16,
          st .x10 .x16, st .x7 .x16 8, ldh .x10 (sArr Public.aN)])) := by
  simp only [VG.Impl.Bignum.AArch64.BlockedRedc.redc, rowBody, startBlock, columnSetup,
    tailBlock, List.append_assoc, List.cons_append, List.nil_append]

/-- Exact Montgomery reduction, plus the complete memory and register frame.
The mathematical relation is conditional on a valid inverse; safe execution
and all frame obligations are unconditional. -/
theorem redc_ok {s : State} {B : Addr} {Z eQ eN k : Nat} {inv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (h8 : s.gpr .x8 = off B eQ) (h12 : s.gpr .x12 = BitVec.ofNat 64 (8 * k))
    (hHdr : 256 ≤ eQ) (hSize : eQ + 128 * k + 16 ≤ Z)
    (hNQ : eN + 64 * k ≤ eQ) (hk : 2 ≤ k) (hk' : 8 * k < 2 ^ 64)
    (hn : word s.mem B (8 * sArr Public.aN) = off B eN)
    (hi : word s.mem B (8 * sMinv) = inv)
    (hw : word s.mem B (8 * sW) = BitVec.ofNat 64 (8 * k)) :
    WP isa VG.Impl.Bignum.AArch64.BlockedRedc.redc s fun t =>
      (((word s.mem B eN).toNat * inv.toNat + 1) % 2 ^ 64 = 0 →
        ∃ q < 2 ^ (64 * (8 * k)), 2 ^ (64 * (8 * k)) *
          wv t.mem B (eQ + 64 * k) (8 * k + 2) =
          wv s.mem B eQ (16 * k) + q * wv s.mem B eN (8 * k)) ∧
      Outside B eQ (128 * k + 16) s.mem t.mem ∧
      t.gpr .x8 = off B (eQ + 64 * k) ∧ t.gpr .x10 = off B eN ∧
      t.gpr .x12 = BitVec.ofNat 64 (8 * k) ∧ t.gpr .x7 = 0 ∧ Keep rowRegs s t := by
  have hns := hs.nowrap
  rewrite [redc_code_eq]
  apply WP.seq
  refine WP.mono (redcInit_ok h12 hk') fun u ⟨⟨hu12, hu10, hum⟩, ku⟩ => ?_
  have huN := (congrArg (fun m : Mem => word m B (8 * sArr Public.aN)) hum).trans hn
  have huI := (congrArg (fun m : Mem => word m B (8 * sMinv)) hum).trans hi
  have huW := (congrArg (fun m : Mem => word m B (8 * sW)) hum).trans hw
  apply WP.seq
  refine WP.mono (redcRows_ok (hs.congr ku.wr) ((ku.gpr .x0 (by decide)).trans h0)
    ((ku.gpr .x7 (by decide)).trans h7) ((ku.gpr .x8 (by decide)).trans h8)
    hu10 hu12 hHdr (by omega) hNQ hk hk' huN huI huW) fun v hI => ?_
  have kuv := ku.trans hI.keep
  have hvW := (hI.frame.word (d := 8 * sW) (by unfold sW; omega)
    (by unfold sW; omega)).trans huW
  change WP isa (.block (([ldh .x12 sW, .lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16] : List Instr) ++
    ([st .x10 .x16, st .x7 .x16 8] : List Instr) ++ [ldh .x10 (sArr Public.aN)])) v _
  rewrite [List.append_assoc]
  apply WP.block_append
  refine WP.mono (endSetup_ok (hs.congr kuv.wr) ((kuv.gpr .x0 (by decide)).trans h0)
    hI.ptr (by omega) hk' hvW) fun c ⟨⟨hc12, hc16, hcm⟩, kc⟩ => ?_
  have kuvc := kuv.trans kc
  apply WP.block_append
  refine WP.mono (endStores_ok (hs.congr kuvc.wr) hc16
    ((kuvc.gpr .x7 (by decide)).trans h7) (by omega)) fun d ⟨⟨hdv, hdo⟩, kd⟩ => ?_
  have kuvcd := kuvc.trans kd
  refine WP.mono (endModulus_ok (hs.congr kuvcd.wr)
    ((kuvcd.gpr .x0 (by decide)).trans h0) (by omega)) fun t ⟨⟨ht10, htm⟩, kt⟩ => ?_
  have vOut : Outside B eQ (128 * k) s.mem v.mem := by
    intro x hx
    exact (hI.frame x hx).trans (congrArg (fun m : Mem => m x) hum)
  have cOut : Outside B eQ (128 * k) s.mem c.mem := by
    intro x hx
    exact (congrArg (fun m : Mem => m x) hcm).trans (vOut x hx)
  have dOut : Outside B eQ (128 * k + 16) s.mem d.mem :=
    (cOut.mono (by omega) (by omega)).trans (hdo.mono (by omega) (by omega))
  have hNfinal := (dOut.word (d := 8 * sArr Public.aN)
    (by unfold sArr Public.aN; omega) (by unfold sArr Public.aN; omega)).trans hn
  refine ⟨?_, ?_, (((kc.trans kd).trans kt).gpr .x8 (by decide)).trans hI.ptr,
    ht10.trans hNfinal, ((kd.trans kt).gpr .x12 (by decide)).trans hc12,
    ((kuvcd.trans kt).gpr .x7 (by decide)).trans h7, (kuvcd.trans kt).mono (by decide)⟩
  · intro hInv
    have hInvU : ((word u.mem B eN).toNat * inv.toNat + 1) % 2 ^ 64 = 0 :=
      (congrArg (fun n => (n * inv.toNat + 1) % 2 ^ 64)
        (congrArg BitVec.toNat (congrArg (fun m : Mem => word m B eN) hum))).trans hInv
    obtain ⟨q, hq, hv⟩ := hI.value hInvU
    rewrite [show 2 * k - k = k by omega] at hv
    have hcV := congrArg (fun m : Mem => wv m B (eQ + 64 * k) (8 * k)) hcm
    have hcC := congrArg BitVec.toNat (kc.gpr .x10 (by decide))
    have hResult := ((congrArg (fun m : Mem => wv m B (eQ + 64 * k) (8 * k + 2)) htm).trans hdv).trans
      ((congrArg (· + 2 ^ (64 * (8 * k)) * (c.gpr .x10).toNat) hcV).trans
        (congrArg (fun p => wv v.mem B (eQ + 64 * k) (8 * k) + 2 ^ (64 * (8 * k)) * p) hcC))
    have huRaw := congrArg (fun m : Mem => wv m B eQ (16 * k)) hum
    have huMod := congrArg (fun m : Mem => wv m B eN (8 * k)) hum
    refine ⟨q, hq, ?_⟩
    exact (congrArg (2 ^ (64 * (8 * k)) * ·) hResult).trans
      (hv.trans ((congrArg (· + q * wv u.mem B eN (8 * k)) huRaw).trans
        (congrArg (fun n => wv s.mem B eQ (16 * k) + q * n) huMod)))
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (dOut x hx)

end VG.Proof.Bignum.AArch64.BlockedRedc
