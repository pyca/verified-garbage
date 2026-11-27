module

public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ed25519.Word64
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCancelTile
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFinish

/-! ### `Bignum.AArch64.BlockedRedcSetup`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

theorem shr3_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self n 8) hn)]

def columnSetup : List Instr :=
  [.addImm .x .x16 .x8 64, .addImm .x .x17 .x17 64,
    ldh .x15 sW, .lsr .x .x15 .x15 3, .subImm .x .x15 .x15 1]

theorem columnSetup_ok {s : State} {B : Addr} {Z eQ eN k : Nat}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h8 : s.gpr .x8 = off B eQ)
    (h17 : s.gpr .x17 = off B eN) (hZ : 256 ≤ Z)
    (hw : word s.mem B (8 * sW) = BitVec.ofNat 64 (8 * k))
    (hk : 2 ≤ k) (hk' : 8 * k < 2 ^ 64) :
    WP isa (.block columnSetup) s fun t =>
      (t.gpr .x16 = off B (eQ + 64) ∧ t.gpr .x17 = off B (eN + 64) ∧
        t.gpr .x15 = BitVec.ofNat 64 (k - 1) ∧ t.mem = s.mem) ∧
      Keep [.x16, .x17, .x15] s t := by
  obtain hd : 8 * k / 8 = k := by omega_using []
  obtain hsub : BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [hk])
  refine WP.keep [.x16, .x17, .x15] ?_ rfl rfl rfl
  brun [columnSetup, h0, h8, h17, hw, hd, shr3_ofNat hk', hsub,
    hs.ld (show 8 * sW + 8 ≤ Z by unfold sW; omega_using [hZ])]

theorem advanceRow_ok {s : State} {B : Addr} {eQ : Nat}
    (h8 : s.gpr .x8 = off B eQ) :
    WP isa (.block [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]) s fun t =>
      (t.gpr .x8 = off B (eQ + 64) ∧ t.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1 ∧
        t.mem = s.mem) ∧ Keep [.x8, .x12] s t := by
  refine WP.keep [.x8, .x12] ?_ rfl rfl rfl
  brun [h8]

theorem redcInit_ok {s : State} {k : Nat}
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (8 * k)) (hk : 8 * k < 2 ^ 64) :
    WP isa (.block [.lsr .x .x12 .x12 3, movi .x10 0]) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 k ∧ t.gpr .x10 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x12, .x10] s t := by
  obtain hd : 8 * k / 8 = k := by omega_using []
  refine WP.keep [.x12, .x10] ?_ rfl rfl rfl
  brun [h12, shr3_ofNat hk, hd]

end VG.Proof.Bignum.AArch64.BlockedRedc

end

end

/-! ### `Bignum.AArch64.BlockedRedcStart`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev startRegs := VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
  VG.Impl.Bignum.AArch64.BlockedRedc.nn ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt ++
  [.x1, .x27, .x15, .x17]

def startBlock : List Instr := VG.Impl.Bignum.AArch64.BlockedRedc.asLoad ++
  [ldh .x17 (sArr Public.aN), ldh .x15 sMinv] ++
  VG.Impl.Bignum.AArch64.BlockedRedc.nsLoad ++
  (List.range 8).flatMap VG.Impl.Bignum.AArch64.BlockedRedc.cancel

theorem startHeader_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 256 ≤ Z) :
    WP isa (.block [ldh .x17 (sArr Public.aN), ldh .x15 sMinv]) s fun t =>
      (t.gpr .x17 = word s.mem B (8 * sArr Public.aN) ∧
       t.gpr .x15 = word s.mem B (8 * sMinv) ∧ t.mem = s.mem) ∧
      Keep [.x17, .x15] s t := by
  refine WP.keep [.x17, .x15] ?_ rfl rfl rfl
  brun [h0, hs.ld (show 8 * sArr Public.aN + 8 ≤ Z by unfold sArr Public.aN; omega_using [hZ]),
    hs.ld (show 8 * sMinv + 8 ≤ Z by unfold sMinv; omega_using [hZ])]

/-- The first block produces all eight reduction coefficients. The frame
holds for every inverse; its arithmetic relation requires a valid inverse. -/
theorem startBlock_ok {s : State} {B : Addr} {Z eQ eN : Nat} {inv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h8 : s.gpr .x8 = off B eQ)
    (h7 : s.gpr .x7 = 0) (hZ : 256 ≤ Z) (hQ : eQ + 64 ≤ Z) (hN : eN + 64 ≤ Z)
    (hQN : eQ + 64 ≤ eN ∨ eN + 64 ≤ eQ)
    (hn : word s.mem B (8 * sArr Public.aN) = off B eN)
    (hi : word s.mem B (8 * sMinv) = inv) :
    WP isa (.block startBlock) s fun t =>
      (((word s.mem B eN).toNat * inv.toNat + 1) % 2 ^ 64 = 0 →
        (2 ^ 64) ^ 8 * blockValue (accumulator t) =
          wv s.mem B eQ 8 + wv t.mem B eQ 8 * wv s.mem B eN 8) ∧
      Outside B eQ 64 s.mem t.mem ∧ t.gpr .x17 = off B eN ∧
      Keep startRegs s t := by
  rewrite [startBlock, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (asLoad_ok hs h8 hQ) fun a ⟨⟨hav, ham, _⟩, ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (startHeader_ok (hs.congr ka.wr) ((ka.gpr .x0 (by decide)).trans h0) hZ)
    fun b ⟨⟨hb17, hb15, hbm⟩, kb⟩ => ?_
  obtain kab := ka.trans kb
  have h17 : b.gpr .x17 = off B eN := hb17.trans
    ((congrArg (fun m : Mem => word m B (8 * sArr Public.aN)) ham).trans hn)
  have h15 : b.gpr .x15 = inv := hb15.trans
    ((congrArg (fun m : Mem => word m B (8 * sMinv)) ham).trans hi)
  apply WP.block_append
  refine WP.mono (nsLoad_ok (hs.congr kab.wr) h17 hN) fun d ⟨⟨hdn, hdm, _⟩, kd⟩ => ?_
  obtain kad := kab.trans kd
  obtain dm := hdm.trans (hbm.trans ham)
  obtain d17 := (kd.gpr .x17 (by decide)).trans h17
  obtain d15 := (kd.gpr .x15 (by decide)).trans h15
  refine WP.mono (cancelPrefix_ok (hs.congr kad.wr)
    ((kad.gpr .x8 (by decide)).trans h8) d17 ((kad.gpr .x7 (by decide)).trans h7)
    hQ (by omega_using [hN]) (by omega_using [hQN]) (Nat.le_refl 8)) fun t hI => ?_
  obtain hA := (congrArg blockValue (keep_accumulator (kb.trans kd) (by decide))).trans
    ((blockValue_congr hav).trans (blockValue_words s.mem B eQ))
  obtain hn0 := congrArg (fun m : Mem => word m B eN) hdm
  obtain hNV : blockValue (operand d (word d.mem B eN)) = wv s.mem B eN 8 :=
    (congrArg (fun n => blockValue (operand d n)) hn0).trans
      ((blockValue_congr hdn).trans ((blockValue_words b.mem B eN).trans
        (congrArg (fun m : Mem => wv m B eN 8) (hbm.trans ham))))
  refine ⟨?_, ?_, (hI.keep.gpr .x17 (by decide)).trans d17,
    (kad.trans hI.keep).mono (by decide)⟩
  · intro hInv
    obtain dN := congrArg BitVec.toNat (congrArg (fun m : Mem => word m B eN) dm)
    obtain dI := congrArg BitVec.toNat d15
    obtain hInvD : ((word d.mem B eN).toNat * (d.gpr .x15).toNat + 1) % 2 ^ 64 = 0 :=
      ((congrArg (fun n => (n * (d.gpr .x15).toNat + 1) % 2 ^ 64) dN).trans
        (congrArg (fun i => ((word s.mem B eN).toNat * i + 1) % 2 ^ 64) dI)).trans hInv
    obtain hv := hI.value hInvD
    obtain hr : 2 ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8
    obtain hp := congrArg (fun r : Nat => r * blockValue (accumulator t)) hr
    exact hp.symm.trans (hv.trans ((congrArg (· + wv t.mem B eQ 8 *
      blockValue (operand d (word d.mem B eN))) hA).trans
        (congrArg (fun n => wv s.mem B eQ 8 + wv t.mem B eQ 8 * n) hNV)))
  · intro x hx
    exact (hI.frame x hx).trans (congrArg (fun m : Mem => m x) dm)

end VG.Proof.Bignum.AArch64.BlockedRedc

end

end


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
  obtain haW := (hao.word (d := 8 * sW) (by unfold sW; omega_arith) (by unfold sW; omega_arith)).trans hw
  refine WP.mono (columnSetup_ok (hs.congr ka.wr) ((ka.gpr .x0 (by decide)).trans h0)
    ((ka.gpr .x8 (by decide)).trans h8) ha17 (by omega_arith) haW hk hk')
    fun b ⟨⟨hb16, hb17, hb15, hbm⟩, kb⟩ => ?_
  obtain kab := ka.trans kb
  apply WP.seq
  refine WP.mono (columns_ok (hs.congr kab.wr) ((kab.gpr .x8 (by decide)).trans h8)
    ((kab.gpr .x7 (by decide)).trans h7) hb16 hb17 hb15
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun c hI => ?_
  obtain kabc := kab.trans hI.keep
  obtain hc16 : c.gpr .x16 = off B (eQ + 64 * k) :=
    hI.ptrT.trans (congrArg (off B) (by omega_arith))
  apply WP.block_append
  refine WP.mono (finishBlock_ok (hs.congr kabc.wr) hc16 (by omega_arith)
    ((kabc.gpr .x10 (by decide)).trans h10) ((kabc.gpr .x7 (by decide)).trans h7))
    fun d ⟨hdv, hd10, hdo, kd⟩ => ?_
  obtain kabcd := kabc.trans kd
  refine WP.mono (advanceRow_ok ((kabcd.gpr .x8 (by decide)).trans h8))
    fun t ⟨⟨ht8, ht12, htm⟩, kt⟩ => ?_
  obtain hr : 2 ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8
  obtain hq := Nat.lt_of_lt_of_le (wv_lt a.mem B eQ 8) (Nat.le_of_eq hr)
  obtain ht10 := congrArg BitVec.toNat (kt.gpr .x10 (by decide))
  obtain hbmOut : Outside B eQ 64 s.mem b.mem := by
    intro x hx
    exact (congrArg (fun m : Mem => m x) hbm).trans (hao x hx)
  obtain hcmOut : Outside B eQ (64 * k) s.mem c.mem :=
    (hbmOut.mono (by omega_arith) (by omega_arith)).trans (hI.frame.mono (by omega_arith) (by omega_arith))
  obtain hdmOut : Outside B eQ (64 * (k + 1)) s.mem d.mem :=
    (hcmOut.mono (by omega_arith) (by omega_arith)).trans (hdo.mono (by omega_arith) (by omega_arith))
  refine ⟨wv a.mem B eQ 8, hq, ?_, ?_, ?_, ht8,
    ht12.trans (congrArg (· - BitVec.ofNat 64 1) (kabcd.gpr .x12 (by decide))),
    (kabcd.trans kt).mono (by decide)⟩
  · intro hInv
    obtain hC := hav hInv
    obtain hbA := congrArg blockValue (keep_accumulator kb (by decide))
    obtain hbQ := congrArg (fun m : Mem => wv m B eQ 8) hbm
    obtain hbT := hbmOut.wv (d := eQ + 64) (k := 8 * (k - 1)) (by omega_arith) (by omega_arith)
    obtain hbN := hbmOut.wv (d := eN + 64) (k := 8 * (k - 1)) (by omega_arith) (by omega_arith)
    have hM := hI.value
    rewrite [hbA, hbT, hbQ, hbN] at hM
    obtain hcT := hcmOut.wv (d := eQ + 64 * k) (k := 8) (by omega_arith) (by omega_arith)
    obtain hF := hdv.trans (congrArg (fun x => blockValue (accumulator c) + x + p.toNat) hcT)
    obtain he := block_row_value hC hM hF
    obtain hdMid := hdo.wv (d := eQ + 64) (k := 8 * (k - 1)) (by omega_arith) (by omega_arith)
    obtain hLast := wv_blocks_succ d.mem B (eQ + 64) (k - 1)
    rewrite [show k - 1 + 1 = k by omega_arith,
      show eQ + 64 + 64 * (k - 1) = eQ + 64 * k by omega_arith, hdMid] at hLast
    obtain hOut := (congrArg (fun m : Mem => wv m B (eQ + 64) (8 * k)) htm).trans hLast
    obtain hInput := wv_blocks_first s.mem B eQ k
    obtain hLastInput := wv_blocks_succ s.mem B (eQ + 64) (k - 1)
    rewrite [show k - 1 + 1 = k by omega_arith,
      show eQ + 64 + 64 * (k - 1) = eQ + 64 * k by omega_arith] at hLastInput
    obtain hMod := wv_blocks_first s.mem B eN (k - 1)
    rewrite [show k - 1 + 1 = k by omega_arith] at hMod
    obtain hPow := pow_blocks_succ (k - 1)
    rewrite [show k - 1 + 1 = k by omega_arith] at hPow
    obtain hPow' := hPow.trans (Nat.mul_comm _ _)
    rewrite [hOut, ht10, hInput, hLastInput, hMod, hPow']
    exact he
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (hdmOut x hx)
  · exact Nat.le_trans (Nat.le_of_eq ht10) hd10

end VG.Proof.Bignum.AArch64.BlockedRedc
