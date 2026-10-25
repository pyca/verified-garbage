module

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBlock
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcStart
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFinish

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev rowRegs := startRegs ++ [.x8, .x10, .x12, .x16]

def rowBody : Prog isa :=
  .seq (.block (startBlock ++ columnSetup))
    (.seq (countLoop .x15 (tailBlock ++ [.addImm .x .x17 .x17 64]))
      (.block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory true ++
        [.adc .x .x10 .x7 .x7] ++ VG.Impl.Bignum.AArch64.BlockedRedc.asStore ++
        [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1])))

/-- A full blocked row preserves the exact Montgomery relation and retains
its outgoing pending carry. All structural conclusions hold for every inverse. -/
theorem rowBody_ok {s : State} {B : Addr} {Z eQ eN k : Nat} {inv : Word} {p : Bool}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h8 : s.gpr .x8 = off B eQ)
    (h7 : s.gpr .x7 = 0) (h10 : s.gpr .x10 = BitVec.ofNat 64 p.toNat)
    (hHdr : 256 ≤ eQ) (hSize : eQ + 64 * (k + 1) ≤ Z)
    (hNQ : eN + 64 * k ≤ eQ) (hk : 2 ≤ k) (hk' : 8 * k < 2 ^ 64)
    (hn : word s.mem B (8 * sArr Public.aN) = off B eN)
    (hi : word s.mem B (8 * sMinv) = inv)
    (hw : word s.mem B (8 * sW) = BitVec.ofNat 64 (8 * k)) :
    WP isa rowBody s fun t => ∃ q < (2 ^ 64) ^ 8,
      (((word s.mem B eN).toNat * inv.toNat + 1) % 2 ^ 64 = 0 →
        (2 ^ 64) ^ 8 * (wv t.mem B (eQ + 64) (8 * k) +
          2 ^ (64 * (8 * k)) * (t.gpr .x10).toNat) =
        wv s.mem B eQ (8 * (k + 1)) + q * wv s.mem B eN (8 * k) +
          2 ^ (64 * (8 * k)) * p.toNat) ∧
      Outside B eQ (64 * (k + 1)) s.mem t.mem ∧ (t.gpr .x10).toNat ≤ 1 ∧
      t.gpr .x8 = off B (eQ + 64) ∧ t.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1 ∧
      Keep rowRegs s t := by
  have hnw := hs.nowrap
  unfold rowBody
  apply WP.seq
  apply WP.block_append
  refine WP.mono (startBlock_ok hs h0 h8 h7 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) hn hi) fun a ⟨hav, hao, ha17, ka⟩ => ?_
  have haW := (hao.word (d := 8 * sW) (by unfold sW; omega_arith) (by unfold sW; omega_arith)).trans hw
  refine WP.mono (columnSetup_ok (hs.congr ka.wr) ((ka.gpr .x0 (by decide)).trans h0)
    ((ka.gpr .x8 (by decide)).trans h8) ha17 (by omega_arith) haW hk hk')
    fun b ⟨⟨hb16, hb17, hb15, hbm⟩, kb⟩ => ?_
  have kab := ka.trans kb
  apply WP.seq
  refine WP.mono (columns_ok (hs.congr kab.wr) ((kab.gpr .x8 (by decide)).trans h8)
    ((kab.gpr .x7 (by decide)).trans h7) hb16 hb17 hb15
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun c hI => ?_
  have kabc := kab.trans hI.keep
  have hc16 : c.gpr .x16 = off B (eQ + 64 * k) :=
    hI.ptrT.trans (congrArg (off B) (by omega_arith))
  apply WP.block_append
  refine WP.mono (finishBlock_ok (hs.congr kabc.wr) hc16 (by omega_arith)
    ((kabc.gpr .x10 (by decide)).trans h10) ((kabc.gpr .x7 (by decide)).trans h7))
    fun d ⟨hdv, hd10, hdo, kd⟩ => ?_
  have kabcd := kabc.trans kd
  refine WP.mono (advanceRow_ok ((kabcd.gpr .x8 (by decide)).trans h8))
    fun t ⟨⟨ht8, ht12, htm⟩, kt⟩ => ?_
  have hr : 2 ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8
  have hq := Nat.lt_of_lt_of_le (wv_lt a.mem B eQ 8) (Nat.le_of_eq hr)
  have ht10 := congrArg BitVec.toNat (kt.gpr .x10 (by decide))
  have hbmOut : Outside B eQ 64 s.mem b.mem := by
    intro x hx
    exact (congrArg (fun m : Mem => m x) hbm).trans (hao x hx)
  have hcmOut : Outside B eQ (64 * k) s.mem c.mem :=
    (hbmOut.mono (by omega_arith) (by omega_arith)).trans (hI.frame.mono (by omega_arith) (by omega_arith))
  have hdmOut : Outside B eQ (64 * (k + 1)) s.mem d.mem :=
    (hcmOut.mono (by omega_arith) (by omega_arith)).trans (hdo.mono (by omega_arith) (by omega_arith))
  refine ⟨wv a.mem B eQ 8, hq, ?_, ?_, ?_, ht8,
    ht12.trans (congrArg (· - BitVec.ofNat 64 1) (kabcd.gpr .x12 (by decide))),
    (kabcd.trans kt).mono (by decide)⟩
  · intro hInv
    have hC := hav hInv
    have hbA := congrArg blockValue (keep_accumulator kb (by decide))
    have hbQ := congrArg (fun m : Mem => wv m B eQ 8) hbm
    have hbT := hbmOut.wv (d := eQ + 64) (k := 8 * (k - 1)) (by omega_arith) (by omega_arith)
    have hbN := hbmOut.wv (d := eN + 64) (k := 8 * (k - 1)) (by omega_arith) (by omega_arith)
    have hM := hI.value
    rewrite [hbA, hbT, hbQ, hbN] at hM
    have hcT := hcmOut.wv (d := eQ + 64 * k) (k := 8) (by omega_arith) (by omega_arith)
    have hF := hdv.trans (congrArg (fun x => blockValue (accumulator c) + x + p.toNat) hcT)
    have he := block_row_value hC hM hF
    have hdMid := hdo.wv (d := eQ + 64) (k := 8 * (k - 1)) (by omega_arith) (by omega_arith)
    have hLast := wv_blocks_succ d.mem B (eQ + 64) (k - 1)
    rewrite [show k - 1 + 1 = k by omega_arith,
      show eQ + 64 + 64 * (k - 1) = eQ + 64 * k by omega_arith, hdMid] at hLast
    have hOut := (congrArg (fun m : Mem => wv m B (eQ + 64) (8 * k)) htm).trans hLast
    have hInput := wv_blocks_first s.mem B eQ k
    have hLastInput := wv_blocks_succ s.mem B (eQ + 64) (k - 1)
    rewrite [show k - 1 + 1 = k by omega_arith,
      show eQ + 64 + 64 * (k - 1) = eQ + 64 * k by omega_arith] at hLastInput
    have hMod := wv_blocks_first s.mem B eN (k - 1)
    rewrite [show k - 1 + 1 = k by omega_arith] at hMod
    have hPow := pow_blocks_succ (k - 1)
    rewrite [show k - 1 + 1 = k by omega_arith] at hPow
    have hPow' := hPow.trans (Nat.mul_comm _ _)
    rewrite [hOut, ht10, hInput, hLastInput, hMod, hPow']
    exact he
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (hdmOut x hx)
  · exact Nat.le_trans (Nat.le_of_eq ht10) hd10

end VG.Proof.Bignum.AArch64.BlockedRedc
